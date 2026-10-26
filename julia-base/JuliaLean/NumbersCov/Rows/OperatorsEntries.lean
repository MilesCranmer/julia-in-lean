import JuliaLean.NumbersCov.Rows.Operators
import JuliaLean.Registry.Types

namespace JuliaLean.NumbersCov.Rows.Operators

open JuliaLean.Registry

def entries : List Entry := [
  { id := "numberscov-operators-s86", juliaFile := "base/operators.jl"
    juliaFns := ["supertype(T::DataType)"]
    statement := "supertype(T::DataType) follows its Julia source body for every allowed input."
    source := "base/operators.jl:86-94; source equation or documented operator invariant"
    status := .proven, prop := ``P86, thm := some ``p86 },
  { id := "numberscov-operators-s95", juliaFile := "base/operators.jl"
    juliaFns := ["getproperty(T::DataType, s::Symbol)"]
    statement := "getproperty(T::DataType, s::Symbol) follows its Julia source body for every allowed input."
    source := "base/operators.jl:95-101; source equation or documented operator invariant"
    status := .proven, prop := ``P95, thm := some ``p95 },
  { id := "numberscov-operators-s102", juliaFile := "base/operators.jl"
    juliaFns := ["supertype(T::UnionAll)"]
    statement := "supertype(T::UnionAll) follows its Julia source body for every allowed input."
    source := "base/operators.jl:102; source equation or documented operator invariant"
    status := .proven, prop := ``P102, thm := some ``p102 },
  { id := "numberscov-operators-s104", juliaFile := "base/operators.jl"
    juliaFns := ["supertype(::TypeEq)"]
    statement := "supertype(::TypeEq) follows its Julia source body for every allowed input."
    source := "base/operators.jl:104; source equation or documented operator invariant"
    status := .proven, prop := ``P104, thm := some ``p104 },
  { id := "numberscov-operators-s105", juliaFile := "base/operators.jl"
    juliaFns := ["supertype(T::Core.TypeEgal)"]
    statement := "supertype(T::Core.TypeEgal) follows its Julia source body for every allowed input."
    source := "base/operators.jl:105; source equation or documented operator invariant"
    status := .proven, prop := ``P105, thm := some ``p105 },
  { id := "numberscov-operators-s196", juliaFile := "base/operators.jl"
    juliaFns := ["isequal(x, y)"]
    statement := "isequal(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:196; source equation or documented operator invariant"
    status := .proven, prop := ``P196, thm := some ``p196 },
  { id := "numberscov-operators-s198", juliaFile := "base/operators.jl"
    juliaFns := ["signequal(x, y)"]
    statement := "signequal(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:198; source equation or documented operator invariant"
    status := .proven, prop := ``P198, thm := some ``p198 },
  { id := "numberscov-operators-s199", juliaFile := "base/operators.jl"
    juliaFns := ["signless(x, y)"]
    statement := "signless(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:199; source equation or documented operator invariant"
    status := .proven, prop := ``P199, thm := some ``p199 },
  { id := "numberscov-operators-s201", juliaFile := "base/operators.jl"
    juliaFns := ["isequal(x::AbstractFloat, y::AbstractFloat)"]
    statement := "isequal(x::AbstractFloat, y::AbstractFloat) follows its Julia source body for every allowed input."
    source := "base/operators.jl:201; source equation or documented operator invariant"
    status := .proven, prop := ``P201, thm := some ``p201 },
  { id := "numberscov-operators-s202", juliaFile := "base/operators.jl"
    juliaFns := ["isequal(x::Real, y::AbstractFloat)"]
    statement := "isequal(x::Real, y::AbstractFloat) follows its Julia source body for every allowed input."
    source := "base/operators.jl:202; source equation or documented operator invariant"
    status := .proven, prop := ``P202, thm := some ``p202 },
  { id := "numberscov-operators-s240", juliaFile := "base/operators.jl"
    juliaFns := ["isless(x::AbstractFloat, y::AbstractFloat)"]
    statement := "isless(x::AbstractFloat, y::AbstractFloat) follows its Julia source body for every allowed input."
    source := "base/operators.jl:240; source equation or documented operator invariant"
    status := .proven, prop := ``P240, thm := some ``p240 },
  { id := "numberscov-operators-s248", juliaFile := "base/operators.jl"
    juliaFns := ["isless(a::Tuple{BitInteger, BitInteger}, b::Tuple{BitInteger, BitInteger})"]
    statement := "isless(a::Tuple{BitInteger, BitInteger}, b::Tuple{BitInteger, BitInteger}) follows its Julia source body for every allowed input."
    source := "base/operators.jl:248-249; source equation or documented operator invariant"
    status := .proven, prop := ``P248, thm := some ``p248 },
  { id := "numberscov-operators-s309", juliaFile := "base/operators.jl"
    juliaFns := ["isunordered(_)"]
    statement := "isunordered(_) follows its Julia source body for every allowed input."
    source := "base/operators.jl:309; source equation or documented operator invariant"
    status := .proven, prop := ``P309, thm := some ``p309 },
  { id := "numberscov-operators-s310", juliaFile := "base/operators.jl"
    juliaFns := ["isunordered(x::AbstractFloat)"]
    statement := "isunordered(x::AbstractFloat) follows its Julia source body for every allowed input."
    source := "base/operators.jl:310; source equation or documented operator invariant"
    status := .proven, prop := ``P310, thm := some ``p310 },
  { id := "numberscov-operators-s313", juliaFile := "base/operators.jl"
    juliaFns := ["==(T::Type, S::Type)"]
    statement := "==(T::Type, S::Type) follows its Julia source body for every allowed input."
    source := "base/operators.jl:313; source equation or documented operator invariant"
    status := .proven, prop := ``P313, thm := some ``p313 },
  { id := "numberscov-operators-s314", juliaFile := "base/operators.jl"
    juliaFns := ["==(T::TypeVar, S::Type)"]
    statement := "==(T::TypeVar, S::Type) follows its Julia source body for every allowed input."
    source := "base/operators.jl:314; source equation or documented operator invariant"
    status := .proven, prop := ``P314, thm := some ``p314 },
  { id := "numberscov-operators-s315", juliaFile := "base/operators.jl"
    juliaFns := ["==(T::Type, S::TypeVar)"]
    statement := "==(T::Type, S::TypeVar) follows its Julia source body for every allowed input."
    source := "base/operators.jl:315; source equation or documented operator invariant"
    status := .proven, prop := ``P315, thm := some ``p315 },
  { id := "numberscov-operators-s338", juliaFile := "base/operators.jl"
    juliaFns := ["!=(x, y)"]
    statement := "!=(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:338; source equation or documented operator invariant"
    status := .proven, prop := ``P338, thm := some ``p338 },
  { id := "numberscov-operators-s417", juliaFile := "base/operators.jl"
    juliaFns := ["<(x, y)"]
    statement := "<(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:417; source equation or documented operator invariant"
    status := .proven, prop := ``P417, thm := some ``p417 },
  { id := "numberscov-operators-s443", juliaFile := "base/operators.jl"
    juliaFns := [">(x, y)"]
    statement := ">(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:443; source equation or documented operator invariant"
    status := .proven, prop := ``P443, thm := some ``p443 },
  { id := "numberscov-operators-s467", juliaFile := "base/operators.jl"
    juliaFns := ["<=(x, y)"]
    statement := "<=(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:467; source equation or documented operator invariant"
    status := .proven, prop := ``P467, thm := some ``p467 },
  { id := "numberscov-operators-s499", juliaFile := "base/operators.jl"
    juliaFns := [">=(x, y)"]
    statement := ">=(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:499; source equation or documented operator invariant"
    status := .proven, prop := ``P499, thm := some ``p499 },
  { id := "numberscov-operators-s526", juliaFile := "base/operators.jl"
    juliaFns := ["cmp(x, y)"]
    statement := "cmp(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:526; source equation or documented operator invariant"
    status := .proven, prop := ``P526, thm := some ``p526 },
  { id := "numberscov-operators-s534", juliaFile := "base/operators.jl"
    juliaFns := ["cmp(<, x, y)"]
    statement := "cmp(<, x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:534; source equation or documented operator invariant"
    status := .proven, prop := ``P534, thm := some ``p534 },
  { id := "numberscov-operators-s588", juliaFile := "base/operators.jl"
    juliaFns := ["minmax(x,y)"]
    statement := "minmax(x,y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:588; source equation or documented operator invariant"
    status := .proven, prop := ``P588, thm := some ``p588 },
  { id := "numberscov-operators-s605", juliaFile := "base/operators.jl"
    juliaFns := ["identity(@nospecialize x)"]
    statement := "identity(@nospecialize x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:605; source equation or documented operator invariant"
    status := .proven, prop := ``P605, thm := some ``p605 },
  { id := "numberscov-operators-s607", juliaFile := "base/operators.jl"
    juliaFns := ["+(x::Number)"]
    statement := "+(x::Number) follows its Julia source body for every allowed input."
    source := "base/operators.jl:607; source equation or documented operator invariant"
    status := .proven, prop := ``P607, thm := some ``p607 },
  { id := "numberscov-operators-s608", juliaFile := "base/operators.jl"
    juliaFns := ["*(x::Number)"]
    statement := "*(x::Number) follows its Julia source body for every allowed input."
    source := "base/operators.jl:608; source equation or documented operator invariant"
    status := .proven, prop := ``P608, thm := some ``p608 },
  { id := "numberscov-operators-s609", juliaFile := "base/operators.jl"
    juliaFns := ["(&)(x::Integer)"]
    statement := "(&)(x::Integer) follows its Julia source body for every allowed input."
    source := "base/operators.jl:609; source equation or documented operator invariant"
    status := .proven, prop := ``P609, thm := some ``p609 },
  { id := "numberscov-operators-s610", juliaFile := "base/operators.jl"
    juliaFns := ["(|)(x::Integer)"]
    statement := "(|)(x::Integer) follows its Julia source body for every allowed input."
    source := "base/operators.jl:610; source equation or documented operator invariant"
    status := .proven, prop := ``P610, thm := some ``p610 },
  { id := "numberscov-operators-s611", juliaFile := "base/operators.jl"
    juliaFns := ["xor(x::Integer)"]
    statement := "xor(x::Integer) follows its Julia source body for every allowed input."
    source := "base/operators.jl:611; source equation or documented operator invariant"
    status := .proven, prop := ``P611, thm := some ``p611 },
  { id := "numberscov-operators-s622", juliaFile := "base/operators.jl"
    juliaFns := ["afoldl(op, a)"]
    statement := "afoldl(op, a) follows its Julia source body for every allowed input."
    source := "base/operators.jl:622; source equation or documented operator invariant"
    status := .proven, prop := ``P622, thm := some ``p622 },
  { id := "numberscov-operators-s623", juliaFile := "base/operators.jl"
    juliaFns := ["afoldl(op, a, bs...)"]
    statement := "afoldl(op, a, bs...) follows its Julia source body for every allowed input."
    source := "base/operators.jl:623-663; source equation or documented operator invariant"
    status := .proven, prop := ``P623, thm := some ``p623 },
  { id := "numberscov-operators-s671", juliaFile := "base/operators.jl"
    juliaFns := ["($op)(a, b, c, xs...)"]
    statement := "($op)(a, b, c, xs...) follows its Julia source body for every allowed input."
    source := "base/operators.jl:671; source equation or documented operator invariant"
    status := .proven, prop := ``P671, thm := some ``p671 },
  { id := "numberscov-operators-s709", juliaFile := "base/operators.jl"
    juliaFns := ["\\(x,y)"]
    statement := "\\(x,y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:709; source equation or documented operator invariant"
    status := .proven, prop := ``P709, thm := some ``p709 },
  { id := "numberscov-operators-s735", juliaFile := "base/operators.jl"
    juliaFns := ["<<(x::Integer, c::Integer)"]
    statement := "<<(x::Integer, c::Integer) follows its Julia source body for every allowed input."
    source := "base/operators.jl:735-740; source equation or documented operator invariant"
    status := .proven, prop := ``P735, thm := some ``p735 },
  { id := "numberscov-operators-s741", juliaFile := "base/operators.jl"
    juliaFns := ["<<(x::Integer, c::Unsigned)"]
    statement := "<<(x::Integer, c::Unsigned) follows its Julia source body for every allowed input."
    source := "base/operators.jl:741-747; source equation or documented operator invariant"
    status := .proven, prop := ``P741, thm := some ``p741 },
  { id := "numberscov-operators-s748", juliaFile := "base/operators.jl"
    juliaFns := ["<<(x::Integer, c::Int)"]
    statement := "<<(x::Integer, c::Int) follows its Julia source body for every allowed input."
    source := "base/operators.jl:748; source equation or documented operator invariant"
    status := .proven, prop := ``P748, thm := some ``p748 },
  { id := "numberscov-operators-s780", juliaFile := "base/operators.jl"
    juliaFns := [">>(x::Integer, c::Integer)"]
    statement := ">>(x::Integer, c::Integer) follows its Julia source body for every allowed input."
    source := "base/operators.jl:780-788; source equation or documented operator invariant"
    status := .proven, prop := ``P780, thm := some ``p780 },
  { id := "numberscov-operators-s789", juliaFile := "base/operators.jl"
    juliaFns := [">>(x::Integer, c::Int)"]
    statement := ">>(x::Integer, c::Int) follows its Julia source body for every allowed input."
    source := "base/operators.jl:789; source equation or documented operator invariant"
    status := .proven, prop := ``P789, thm := some ``p789 },
  { id := "numberscov-operators-s818", juliaFile := "base/operators.jl"
    juliaFns := [">>>(x::Integer, c::Integer)"]
    statement := ">>>(x::Integer, c::Integer) follows its Julia source body for every allowed input."
    source := "base/operators.jl:818-821; source equation or documented operator invariant"
    status := .proven, prop := ``P818, thm := some ``p818 },
  { id := "numberscov-operators-s822", juliaFile := "base/operators.jl"
    juliaFns := [">>>(x::Integer, c::Unsigned)"]
    statement := ">>>(x::Integer, c::Unsigned) follows its Julia source body for every allowed input."
    source := "base/operators.jl:822-828; source equation or documented operator invariant"
    status := .proven, prop := ``P822, thm := some ``p822 },
  { id := "numberscov-operators-s829", juliaFile := "base/operators.jl"
    juliaFns := [">>>(x::Integer, c::Int)"]
    statement := ">>>(x::Integer, c::Int) follows its Julia source body for every allowed input."
    source := "base/operators.jl:829; source equation or documented operator invariant"
    status := .proven, prop := ``P829, thm := some ``p829 },
  { id := "numberscov-operators-s914", juliaFile := "base/operators.jl"
    juliaFns := ["mod1(x::T, y::T) where {T<:Real}"]
    statement := "mod1(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/operators.jl:914; source equation or documented operator invariant"
    status := .proven, prop := ``P914, thm := some ``p914 },
  { id := "numberscov-operators-s943", juliaFile := "base/operators.jl"
    juliaFns := ["cldmod1(x, y)"]
    statement := "cldmod1(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:943; source equation or documented operator invariant"
    status := .proven, prop := ``P943, thm := some ``p943 },
  { id := "numberscov-operators-s952", juliaFile := "base/operators.jl"
    juliaFns := ["fldmod1(x, y)"]
    statement := "fldmod1(x, y) follows its Julia source body for every allowed input."
    source := "base/operators.jl:952; source equation or documented operator invariant"
    status := .proven, prop := ``P952, thm := some ``p952 },
  { id := "numberscov-operators-s975", juliaFile := "base/operators.jl"
    juliaFns := ["widen(x::T) where {T}"]
    statement := "widen(x::T) where {T} follows its Julia source body for every allowed input."
    source := "base/operators.jl:975; source equation or documented operator invariant"
    status := .proven, prop := ``P975, thm := some ``p975 },
  { id := "numberscov-operators-s976", juliaFile := "base/operators.jl"
    juliaFns := ["widen(x::Type{T}) where {T}"]
    statement := "widen(x::Type{T}) where {T} follows its Julia source body for every allowed input."
    source := "base/operators.jl:976; source equation or documented operator invariant"
    status := .proven, prop := ``P976, thm := some ``p976 },
  { id := "numberscov-operators-s977", juliaFile := "base/operators.jl"
    juliaFns := ["widen(x::Type{Union{}}, slurp...)"]
    statement := "widen(x::Type{Union{}}, slurp...) follows its Julia source body for every allowed input."
    source := "base/operators.jl:977; source equation or documented operator invariant"
    status := .proven, prop := ``P977, thm := some ``p977 },
  { id := "numberscov-operators-s1001", juliaFile := "base/operators.jl"
    juliaFns := ["|>(x, f)"]
    statement := "|>(x, f) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1001; source equation or documented operator invariant"
    status := .proven, prop := ``P1001, thm := some ``p1001 },
  { id := "numberscov-operators-s1003", juliaFile := "base/operators.jl"
    juliaFns := ["_stable_typeof(x)"]
    statement := "_stable_typeof(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1003; source equation or documented operator invariant"
    status := .proven, prop := ``P1003, thm := some ``p1003 },
  { id := "numberscov-operators-s1004", juliaFile := "base/operators.jl"
    juliaFns := ["_stable_typeof(::Type{T}) where {T}"]
    statement := "_stable_typeof(::Type{T}) where {T} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1004; source equation or documented operator invariant"
    status := .proven, prop := ``P1004, thm := some ``p1004 },
  { id := "numberscov-operators-s1031", juliaFile := "base/operators.jl"
    juliaFns := ["Returns{V}(value) where {V}"]
    statement := "Returns{V}(value) where {V} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1031; source equation or documented operator invariant"
    status := .proven, prop := ``P1031, thm := some ``p1031 },
  { id := "numberscov-operators-s1032", juliaFile := "base/operators.jl"
    juliaFns := ["Returns(value)"]
    statement := "Returns(value) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1032; source equation or documented operator invariant"
    status := .proven, prop := ``P1032, thm := some ``p1032 },
  { id := "numberscov-operators-s1035", juliaFile := "base/operators.jl"
    juliaFns := ["(obj::Returns)(@nospecialize(args...); @nospecialize(kw...))"]
    statement := "(obj::Returns)(@nospecialize(args...); @nospecialize(kw...)) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1035; source equation or documented operator invariant"
    status := .proven, prop := ``P1035, thm := some ``p1035 },
  { id := "numberscov-operators-s1121", juliaFile := "base/operators.jl"
    juliaFns := ["ComposedFunction{O, I}(outer, inner) where {O, I}"]
    statement := "ComposedFunction{O, I}(outer, inner) where {O, I} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1121; source equation or documented operator invariant"
    status := .proven, prop := ``P1121, thm := some ``p1121 },
  { id := "numberscov-operators-s1122", juliaFile := "base/operators.jl"
    juliaFns := ["ComposedFunction(outer, inner)"]
    statement := "ComposedFunction(outer, inner) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1122; source equation or documented operator invariant"
    status := .proven, prop := ``P1122, thm := some ``p1122 },
  { id := "numberscov-operators-s1125", juliaFile := "base/operators.jl"
    juliaFns := ["(c::ComposedFunction)(x...; kw...)"]
    statement := "(c::ComposedFunction)(x...; kw...) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1125; source equation or documented operator invariant"
    status := .proven, prop := ``P1125, thm := some ``p1125 },
  { id := "numberscov-operators-s1126", juliaFile := "base/operators.jl"
    juliaFns := ["unwrap_composed(c::ComposedFunction)"]
    statement := "unwrap_composed(c::ComposedFunction) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1126; source equation or documented operator invariant"
    status := .proven, prop := ``P1126, thm := some ``p1126 },
  { id := "numberscov-operators-s1127", juliaFile := "base/operators.jl"
    juliaFns := ["unwrap_composed(c)"]
    statement := "unwrap_composed(c) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1127; source equation or documented operator invariant"
    status := .proven, prop := ``P1127, thm := some ``p1127 },
  { id := "numberscov-operators-s1128", juliaFile := "base/operators.jl"
    juliaFns := ["call_composed(fs, x, kw)"]
    statement := "call_composed(fs, x, kw) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1128; source equation or documented operator invariant"
    status := .proven, prop := ``P1128, thm := some ``p1128 },
  { id := "numberscov-operators-s1129", juliaFile := "base/operators.jl"
    juliaFns := ["call_composed(fs::Tuple{Any}, x, kw)"]
    statement := "call_composed(fs::Tuple{Any}, x, kw) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1129; source equation or documented operator invariant"
    status := .proven, prop := ``P1129, thm := some ``p1129 },
  { id := "numberscov-operators-s1132", juliaFile := "base/operators.jl"
    juliaFns := ["(::Constructor{F})(args...; kw...) where {F}"]
    statement := "(::Constructor{F})(args...; kw...) where {F} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1132; source equation or documented operator invariant"
    status := .proven, prop := ``P1132, thm := some ``p1132 },
  { id := "numberscov-operators-s1133", juliaFile := "base/operators.jl"
    juliaFns := ["maybeconstructor(::Type{F}) where {F}"]
    statement := "maybeconstructor(::Type{F}) where {F} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1133; source equation or documented operator invariant"
    status := .proven, prop := ``P1133, thm := some ``p1133 },
  { id := "numberscov-operators-s1134", juliaFile := "base/operators.jl"
    juliaFns := ["maybeconstructor(f)"]
    statement := "maybeconstructor(f) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1134; source equation or documented operator invariant"
    status := .proven, prop := ``P1134, thm := some ``p1134 },
  { id := "numberscov-operators-s1136", juliaFile := "base/operators.jl"
    juliaFns := ["∘(f)"]
    statement := "∘(f) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1136; source equation or documented operator invariant"
    status := .proven, prop := ``P1136, thm := some ``p1136 },
  { id := "numberscov-operators-s1137", juliaFile := "base/operators.jl"
    juliaFns := ["∘(f, g)"]
    statement := "∘(f, g) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1137; source equation or documented operator invariant"
    status := .proven, prop := ``P1137, thm := some ``p1137 },
  { id := "numberscov-operators-s1138", juliaFile := "base/operators.jl"
    juliaFns := ["∘(f, g, h...)"]
    statement := "∘(f, g, h...) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1138; source equation or documented operator invariant"
    status := .proven, prop := ``P1138, thm := some ``p1138 },
  { id := "numberscov-operators-s1140", juliaFile := "base/operators.jl"
    juliaFns := ["show(io::IO, c::ComposedFunction)"]
    statement := "show(io::IO, c::ComposedFunction) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1140-1144; source equation or documented operator invariant"
    status := .proven, prop := ``P1140, thm := some ``p1140 },
  { id := "numberscov-operators-s1147", juliaFile := "base/operators.jl"
    juliaFns := ["show(io::IO, c::ComposedFunction{typeof(!)})"]
    statement := "show(io::IO, c::ComposedFunction{typeof(!)}) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1147-1150; source equation or documented operator invariant"
    status := .proven, prop := ``P1147, thm := some ``p1147 },
  { id := "numberscov-operators-s1152", juliaFile := "base/operators.jl"
    juliaFns := ["_showcomposed(io::IO, x)"]
    statement := "_showcomposed(io::IO, x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1152; source equation or documented operator invariant"
    status := .proven, prop := ``P1152, thm := some ``p1152 },
  { id := "numberscov-operators-s1154", juliaFile := "base/operators.jl"
    juliaFns := ["_showcomposed(io::IO, f::Function)"]
    statement := "_showcomposed(io::IO, f::Function) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1154; source equation or documented operator invariant"
    status := .proven, prop := ``P1154, thm := some ``p1154 },
  { id := "numberscov-operators-s1156", juliaFile := "base/operators.jl"
    juliaFns := ["_showcomposed(io::IO, f::ComposedFunction)"]
    statement := "_showcomposed(io::IO, f::ComposedFunction) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1156; source equation or documented operator invariant"
    status := .proven, prop := ``P1156, thm := some ``p1156 },
  { id := "numberscov-operators-s1158", juliaFile := "base/operators.jl"
    juliaFns := ["_showcomposed(io::IO, f::ComposedFunction{typeof(!)})"]
    statement := "_showcomposed(io::IO, f::ComposedFunction{typeof(!)}) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1158; source equation or documented operator invariant"
    status := .proven, prop := ``P1158, thm := some ``p1158 },
  { id := "numberscov-operators-s1182", juliaFile := "base/operators.jl"
    juliaFns := ["!(f::Function)"]
    statement := "!(f::Function) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1182; source equation or documented operator invariant"
    status := .proven, prop := ``P1182, thm := some ``p1182 },
  { id := "numberscov-operators-s1183", juliaFile := "base/operators.jl"
    juliaFns := ["!(f::ComposedFunction{typeof(!)})"]
    statement := "!(f::ComposedFunction{typeof(!)}) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1183; source equation or documented operator invariant"
    status := .proven, prop := ``P1183, thm := some ``p1183 },
  { id := "numberscov-operators-s1206", juliaFile := "base/operators.jl"
    juliaFns := ["Fix{N}(f::F, x) where {N,F}"]
    statement := "Fix{N}(f::F, x) where {N,F} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1206-1213; source equation or documented operator invariant"
    status := .proven, prop := ``P1206, thm := some ``p1206 },
  { id := "numberscov-operators-s1216", juliaFile := "base/operators.jl"
    juliaFns := ["(f::Fix{N})(args::Vararg{Any,M}; kws...) where {N,M}"]
    statement := "(f::Fix{N})(args::Vararg{Any,M}; kws...) where {N,M} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1216-1220; source equation or documented operator invariant"
    status := .proven, prop := ``P1216, thm := some ``p1216 },
  { id := "numberscov-operators-s1223", juliaFile := "base/operators.jl"
    juliaFns := ["(f::Fix{1})(arg; kws...)"]
    statement := "(f::Fix{1})(arg; kws...) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1223; source equation or documented operator invariant"
    status := .proven, prop := ``P1223, thm := some ``p1223 },
  { id := "numberscov-operators-s1224", juliaFile := "base/operators.jl"
    juliaFns := ["(f::Fix{2})(arg; kws...)"]
    statement := "(f::Fix{2})(arg; kws...) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1224; source equation or documented operator invariant"
    status := .proven, prop := ``P1224, thm := some ``p1224 },
  { id := "numberscov-operators-s1226", juliaFile := "base/operators.jl"
    juliaFns := ["Base.show(io::IO, fix::Fix{N}) where {N}"]
    statement := "Base.show(io::IO, fix::Fix{N}) where {N} follows its Julia source body for every allowed input."
    source := "base/operators.jl:1226-1237; source equation or documented operator invariant"
    status := .proven, prop := ``P1226, thm := some ``p1226 },
  { id := "numberscov-operators-s1259", juliaFile := "base/operators.jl"
    juliaFns := ["isequal(x)"]
    statement := "isequal(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1259; source equation or documented operator invariant"
    status := .proven, prop := ``P1259, thm := some ``p1259 },
  { id := "numberscov-operators-s1270", juliaFile := "base/operators.jl"
    juliaFns := ["==(x)"]
    statement := "==(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1270; source equation or documented operator invariant"
    status := .proven, prop := ``P1270, thm := some ``p1270 },
  { id := "numberscov-operators-s1283", juliaFile := "base/operators.jl"
    juliaFns := ["!=(x)"]
    statement := "!=(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1283; source equation or documented operator invariant"
    status := .proven, prop := ``P1283, thm := some ``p1283 },
  { id := "numberscov-operators-s1296", juliaFile := "base/operators.jl"
    juliaFns := [">=(x)"]
    statement := ">=(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1296; source equation or documented operator invariant"
    status := .proven, prop := ``P1296, thm := some ``p1296 },
  { id := "numberscov-operators-s1309", juliaFile := "base/operators.jl"
    juliaFns := ["<=(x)"]
    statement := "<=(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1309; source equation or documented operator invariant"
    status := .proven, prop := ``P1309, thm := some ``p1309 },
  { id := "numberscov-operators-s1322", juliaFile := "base/operators.jl"
    juliaFns := [">(x)"]
    statement := ">(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1322; source equation or documented operator invariant"
    status := .proven, prop := ``P1322, thm := some ``p1322 },
  { id := "numberscov-operators-s1335", juliaFile := "base/operators.jl"
    juliaFns := ["<(x)"]
    statement := "<(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1335; source equation or documented operator invariant"
    status := .proven, prop := ``P1335, thm := some ``p1335 },
  { id := "numberscov-operators-s1366", juliaFile := "base/operators.jl"
    juliaFns := ["splat(f)"]
    statement := "splat(f) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1366; source equation or documented operator invariant"
    status := .proven, prop := ``P1366, thm := some ``p1366 },
  { id := "numberscov-operators-s1384", juliaFile := "base/operators.jl"
    juliaFns := ["Splat(f)"]
    statement := "Splat(f) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1384; source equation or documented operator invariant"
    status := .proven, prop := ``P1384, thm := some ``p1384 },
  { id := "numberscov-operators-s1386", juliaFile := "base/operators.jl"
    juliaFns := ["(s::Splat)(args)"]
    statement := "(s::Splat)(args) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1386; source equation or documented operator invariant"
    status := .proven, prop := ``P1386, thm := some ``p1386 },
  { id := "numberscov-operators-s1387", juliaFile := "base/operators.jl"
    juliaFns := ["show(io::IO, s::Splat)"]
    statement := "show(io::IO, s::Splat) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1387; source equation or documented operator invariant"
    status := .proven, prop := ``P1387, thm := some ``p1387 },
  { id := "numberscov-operators-s1415", juliaFile := "base/operators.jl"
    juliaFns := ["unsplat(f)"]
    statement := "unsplat(f) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1415; source equation or documented operator invariant"
    status := .proven, prop := ``P1415, thm := some ``p1415 },
  { id := "numberscov-operators-s1416", juliaFile := "base/operators.jl"
    juliaFns := ["unsplat(s::Splat)"]
    statement := "unsplat(s::Splat) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1416; source equation or documented operator invariant"
    status := .proven, prop := ``P1416, thm := some ``p1416 },
  { id := "numberscov-operators-s1417", juliaFile := "base/operators.jl"
    juliaFns := ["splat(f::ComposedFunction{<:Any,typeof(tuple)})"]
    statement := "splat(f::ComposedFunction{<:Any,typeof(tuple)}) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1417; source equation or documented operator invariant"
    status := .proven, prop := ``P1417, thm := some ``p1417 },
  { id := "numberscov-operators-s1438", juliaFile := "base/operators.jl"
    juliaFns := ["tap(f)"]
    statement := "tap(f) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1438; source equation or documented operator invariant"
    status := .proven, prop := ``P1438, thm := some ``p1438 },
  { id := "numberscov-operators-s1453", juliaFile := "base/operators.jl"
    juliaFns := ["in(x)"]
    statement := "in(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1453; source equation or documented operator invariant"
    status := .proven, prop := ``P1453, thm := some ``p1453 },
  { id := "numberscov-operators-s1455", juliaFile := "base/operators.jl"
    juliaFns := ["in(x, itr::Any)"]
    statement := "in(x, itr::Any) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1455; source equation or documented operator invariant"
    status := .proven, prop := ``P1455, thm := some ``p1455 },
  { id := "numberscov-operators-s1477", juliaFile := "base/operators.jl"
    juliaFns := ["∉(x, itr)"]
    statement := "∉(x, itr) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1477; source equation or documented operator invariant"
    status := .proven, prop := ``P1477, thm := some ``p1477 },
  { id := "numberscov-operators-s1478", juliaFile := "base/operators.jl"
    juliaFns := ["∉(itr)"]
    statement := "∉(itr) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1478; source equation or documented operator invariant"
    status := .proven, prop := ``P1478, thm := some ``p1478 },
  { id := "numberscov-operators-s1486", juliaFile := "base/operators.jl"
    juliaFns := ["∋(itr, x)"]
    statement := "∋(itr, x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1486; source equation or documented operator invariant"
    status := .proven, prop := ``P1486, thm := some ``p1486 },
  { id := "numberscov-operators-s1497", juliaFile := "base/operators.jl"
    juliaFns := ["∋(x)"]
    statement := "∋(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1497; source equation or documented operator invariant"
    status := .proven, prop := ``P1497, thm := some ``p1497 },
  { id := "numberscov-operators-s1499", juliaFile := "base/operators.jl"
    juliaFns := ["∌(itr, x)"]
    statement := "∌(itr, x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1499; source equation or documented operator invariant"
    status := .proven, prop := ``P1499, thm := some ``p1499 },
  { id := "numberscov-operators-s1500", juliaFile := "base/operators.jl"
    juliaFns := ["∌(x)"]
    statement := "∌(x) follows its Julia source body for every allowed input."
    source := "base/operators.jl:1500; source equation or documented operator invariant"
    status := .proven, prop := ``P1500, thm := some ``p1500 }
]

end JuliaLean.NumbersCov.Rows.Operators
