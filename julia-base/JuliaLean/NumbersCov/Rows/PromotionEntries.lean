import JuliaLean.NumbersCov.Rows.Promotion
import JuliaLean.Registry.Types

namespace JuliaLean.NumbersCov.Rows.Promotion
open JuliaLean.Registry

def entries : List Entry := [
  { id := "numberscov-promotion-s20", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin()"]
    statement := "typejoin() follows its Julia source body for every allowed input."
    source := "base/promotion.jl:20; source equation or documented promotion invariant"
    status := .proven, prop := ``P20, thm := some ``p20 },
  { id := "numberscov-promotion-s21", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin(@nospecialize(t))"]
    statement := "typejoin(@nospecialize(t)) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:21; source equation or documented promotion invariant"
    status := .proven, prop := ``P21, thm := some ``p21 },
  { id := "numberscov-promotion-s22", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin(@nospecialize(t), @nospecialize(s), @nospecialize(u))"]
    statement := "typejoin(@nospecialize(t), @nospecialize(s), @nospecialize(u)) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:22; source equation or documented promotion invariant"
    status := .proven, prop := ``P22, thm := some ``p22 },
  { id := "numberscov-promotion-s23", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin(@nospecialize(t), @nospecialize(s), @nospecialize(u), ts...)"]
    statement := "typejoin(@nospecialize(t), @nospecialize(s), @nospecialize(u), ts...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:23; source equation or documented promotion invariant"
    status := .proven, prop := ``P23, thm := some ``p23 },
  { id := "numberscov-promotion-s25", juliaFile := "base/promotion.jl"
    juliaFns := ["_has_ancestor_typename(@nospecialize(a), name::Core.TypeName)"]
    statement := "_has_ancestor_typename(@nospecialize(a), name::Core.TypeName) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:25-35; source equation or documented promotion invariant"
    status := .proven, prop := ``P25, thm := some ``p25 },
  { id := "numberscov-promotion-s37", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin(@nospecialize(a), @nospecialize(b))"]
    statement := "typejoin(@nospecialize(a), @nospecialize(b)) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:37-160; source equation or documented promotion invariant"
    status := .proven, prop := ``P37, thm := some ``p37 },
  { id := "numberscov-promotion-s166", juliaFile := "base/promotion.jl"
    juliaFns := ["typesplit(@nospecialize(a), @nospecialize(b))"]
    statement := "typesplit(@nospecialize(a), @nospecialize(b)) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:166-177; source equation or documented promotion invariant"
    status := .proven, prop := ``P166, thm := some ``p166 },
  { id := "numberscov-promotion-s198", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_typejoin(@nospecialize(a), @nospecialize(b))"]
    statement := "promote_typejoin(@nospecialize(a), @nospecialize(b)) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:198-201; source equation or documented promotion invariant"
    status := .proven, prop := ``P198, thm := some ``p198 },
  { id := "numberscov-promotion-s202", juliaFile := "base/promotion.jl"
    juliaFns := ["_promote_typesubtract(@nospecialize(a))"]
    statement := "_promote_typesubtract(@nospecialize(a)) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:202-207; source equation or documented promotion invariant"
    status := .proven, prop := ``P202, thm := some ``p202 },
  { id := "numberscov-promotion-s209", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_typejoin_union(::Type{T}) where T"]
    statement := "promote_typejoin_union(::Type{T}) where T follows its Julia source body for every allowed input."
    source := "base/promotion.jl:209-224; source equation or documented promotion invariant"
    status := .proven, prop := ``P209, thm := some ``p209 },
  { id := "numberscov-promotion-s226", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin_union_tuple(T::DataType)"]
    statement := "typejoin_union_tuple(T::DataType) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:226-253; source equation or documented promotion invariant"
    status := .proven, prop := ``P226, thm := some ``p226 },
  { id := "numberscov-promotion-s256", juliaFile := "base/promotion.jl"
    juliaFns := ["full_va_len(p::Core.SimpleVector)"]
    statement := "full_va_len(p::Core.SimpleVector) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:256-267; source equation or documented promotion invariant"
    status := .proven, prop := ``P256, thm := some ``p256 },
  { id := "numberscov-promotion-s270", juliaFile := "base/promotion.jl"
    juliaFns := ["tailjoin(A::SimpleVector, i::Int)"]
    statement := "tailjoin(A::SimpleVector, i::Int) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:270-280; source equation or documented promotion invariant"
    status := .proven, prop := ``P270, thm := some ``p270 },
  { id := "numberscov-promotion-s326", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type()"]
    statement := "promote_type() follows its Julia source body for every allowed input."
    source := "base/promotion.jl:326; source equation or documented promotion invariant"
    status := .proven, prop := ``P326, thm := some ``p326 },
  { id := "numberscov-promotion-s327", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(T)"]
    statement := "promote_type(T) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:327; source equation or documented promotion invariant"
    status := .proven, prop := ``P327, thm := some ``p327 },
  { id := "numberscov-promotion-s328", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(T, S, U)"]
    statement := "promote_type(T, S, U) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:328; source equation or documented promotion invariant"
    status := .proven, prop := ``P328, thm := some ``p328 },
  { id := "numberscov-promotion-s329", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(T, S, U, V...)"]
    statement := "promote_type(T, S, U, V...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:329; source equation or documented promotion invariant"
    status := .proven, prop := ``P329, thm := some ``p329 },
  { id := "numberscov-promotion-s331", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{Bottom}, ::Type{Bottom})"]
    statement := "promote_type(::Type{Bottom}, ::Type{Bottom}) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:331; source equation or documented promotion invariant"
    status := .proven, prop := ``P331, thm := some ``p331 },
  { id := "numberscov-promotion-s332", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{T}, ::Type{T}) where {T}"]
    statement := "promote_type(::Type{T}, ::Type{T}) where {T} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:332; source equation or documented promotion invariant"
    status := .proven, prop := ``P332, thm := some ``p332 },
  { id := "numberscov-promotion-s333", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{T}, ::Type{Bottom}) where {T}"]
    statement := "promote_type(::Type{T}, ::Type{Bottom}) where {T} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:333; source equation or documented promotion invariant"
    status := .proven, prop := ``P333, thm := some ``p333 },
  { id := "numberscov-promotion-s334", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{Bottom}, ::Type{T}) where {T}"]
    statement := "promote_type(::Type{Bottom}, ::Type{T}) where {T} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:334; source equation or documented promotion invariant"
    status := .proven, prop := ``P334, thm := some ``p334 },
  { id := "numberscov-promotion-s336", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{T}, ::Type{S}) where {T,S}"]
    statement := "promote_type(::Type{T}, ::Type{S}) where {T,S} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:336-344; source equation or documented promotion invariant"
    status := .proven, prop := ``P336, thm := some ``p336 },
  { id := "numberscov-promotion-s355", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_rule(::Type, ::Type)"]
    statement := "promote_rule(::Type, ::Type) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:355; source equation or documented promotion invariant"
    status := .proven, prop := ``P355, thm := some ``p355 },
  { id := "numberscov-promotion-s358", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_rule(::Type{Bottom}, slurp...)"]
    statement := "promote_rule(::Type{Bottom}, slurp...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:358; source equation or documented promotion invariant"
    status := .proven, prop := ``P358, thm := some ``p358 },
  { id := "numberscov-promotion-s359", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_rule(::Type{Bottom}, ::Type{Bottom}, slurp...)"]
    statement := "promote_rule(::Type{Bottom}, ::Type{Bottom}, slurp...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:359; source equation or documented promotion invariant"
    status := .proven, prop := ``P359, thm := some ``p359 },
  { id := "numberscov-promotion-s360", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_rule(::Type{Bottom}, ::Type{T}, slurp...) where {T}"]
    statement := "promote_rule(::Type{Bottom}, ::Type{T}, slurp...) where {T} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:360; source equation or documented promotion invariant"
    status := .proven, prop := ``P360, thm := some ``p360 },
  { id := "numberscov-promotion-s361", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_rule(::Type{T}, ::Type{Bottom}, slurp...) where {T}"]
    statement := "promote_rule(::Type{T}, ::Type{Bottom}, slurp...) where {T} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:361; source equation or documented promotion invariant"
    status := .proven, prop := ``P361, thm := some ``p361 },
  { id := "numberscov-promotion-s363", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_result(::Type,::Type,::Type{T},::Type{S}) where {T,S}"]
    statement := "promote_result(::Type,::Type,::Type{T},::Type{S}) where {T,S} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:363; source equation or documented promotion invariant"
    status := .proven, prop := ``P363, thm := some ``p363 },
  { id := "numberscov-promotion-s366", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_result(::Type{T},::Type{S},::Type{Bottom},::Type{Bottom}) where {T,S}"]
    statement := "promote_result(::Type{T},::Type{S},::Type{Bottom},::Type{Bottom}) where {T,S} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:366; source equation or documented promotion invariant"
    status := .proven, prop := ``P366, thm := some ``p366 },
  { id := "numberscov-promotion-s397", juliaFile := "base/promotion.jl"
    juliaFns := ["_promote(x::T, y::S) where {T,S}"]
    statement := "_promote(x::T, y::S) where {T,S} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:397-401; source equation or documented promotion invariant"
    status := .proven, prop := ``P397, thm := some ``p397 },
  { id := "numberscov-promotion-s402", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_typeof(x)"]
    statement := "promote_typeof(x) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:402; source equation or documented promotion invariant"
    status := .proven, prop := ``P402, thm := some ``p402 },
  { id := "numberscov-promotion-s403", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_typeof(x, y)"]
    statement := "promote_typeof(x, y) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:403; source equation or documented promotion invariant"
    status := .proven, prop := ``P403, thm := some ``p403 },
  { id := "numberscov-promotion-s404", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_typeof(x, y, z)"]
    statement := "promote_typeof(x, y, z) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:404; source equation or documented promotion invariant"
    status := .proven, prop := ``P404, thm := some ``p404 },
  { id := "numberscov-promotion-s405", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_typeof(x, y, z, a...)"]
    statement := "promote_typeof(x, y, z, a...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:405; source equation or documented promotion invariant"
    status := .proven, prop := ``P405, thm := some ``p405 },
  { id := "numberscov-promotion-s406", juliaFile := "base/promotion.jl"
    juliaFns := ["_promote(x, y, z)"]
    statement := "_promote(x, y, z) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:406-410; source equation or documented promotion invariant"
    status := .proven, prop := ``P406, thm := some ``p406 },
  { id := "numberscov-promotion-s411", juliaFile := "base/promotion.jl"
    juliaFns := ["_promote(x, y, zs...)"]
    statement := "_promote(x, y, zs...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:411-415; source equation or documented promotion invariant"
    status := .proven, prop := ``P411, thm := some ``p411 },
  { id := "numberscov-promotion-s420", juliaFile := "base/promotion.jl"
    juliaFns := ["promote()"]
    statement := "promote() follows its Julia source body for every allowed input."
    source := "base/promotion.jl:420; source equation or documented promotion invariant"
    status := .proven, prop := ``P420, thm := some ``p420 },
  { id := "numberscov-promotion-s421", juliaFile := "base/promotion.jl"
    juliaFns := ["promote(x)"]
    statement := "promote(x) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:421; source equation or documented promotion invariant"
    status := .proven, prop := ``P421, thm := some ``p421 },
  { id := "numberscov-promotion-s423", juliaFile := "base/promotion.jl"
    juliaFns := ["promote(x, y)"]
    statement := "promote(x, y) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:423-428; source equation or documented promotion invariant"
    status := .proven, prop := ``P423, thm := some ``p423 },
  { id := "numberscov-promotion-s429", juliaFile := "base/promotion.jl"
    juliaFns := ["promote(x, y, z)"]
    statement := "promote(x, y, z) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:429-434; source equation or documented promotion invariant"
    status := .proven, prop := ``P429, thm := some ``p429 },
  { id := "numberscov-promotion-s435", juliaFile := "base/promotion.jl"
    juliaFns := ["promote(x, y, z, a...)"]
    statement := "promote(x, y, z, a...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:435-439; source equation or documented promotion invariant"
    status := .proven, prop := ``P435, thm := some ``p435 },
  { id := "numberscov-promotion-s441", juliaFile := "base/promotion.jl"
    juliaFns := ["promote(x::T, y::T, zs::T...) where {T}"]
    statement := "promote(x::T, y::T, zs::T...) where {T} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:441; source equation or documented promotion invariant"
    status := .proven, prop := ``P441, thm := some ``p441 },
  { id := "numberscov-promotion-s443", juliaFile := "base/promotion.jl"
    juliaFns := ["not_sametype(x::T, y::T) where {T}"]
    statement := "not_sametype(x::T, y::T) where {T} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:443; source equation or documented promotion invariant"
    status := .proven, prop := ``P443, thm := some ``p443 },
  { id := "numberscov-promotion-s445", juliaFile := "base/promotion.jl"
    juliaFns := ["not_sametype(x, y)"]
    statement := "not_sametype(x, y) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:445; source equation or documented promotion invariant"
    status := .proven, prop := ``P445, thm := some ``p445 },
  { id := "numberscov-promotion-s447", juliaFile := "base/promotion.jl"
    juliaFns := ["sametype_error(input)"]
    statement := "sametype_error(input) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:447-452; source equation or documented promotion invariant"
    status := .proven, prop := ``P447, thm := some ``p447 },
  { id := "numberscov-promotion-s454", juliaFile := "base/promotion.jl"
    juliaFns := ["+(x::Number, y::Number)"]
    statement := "+(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:454; source equation or documented promotion invariant"
    status := .proven, prop := ``P454, thm := some ``p454 },
  { id := "numberscov-promotion-s455", juliaFile := "base/promotion.jl"
    juliaFns := ["*(x::Number, y::Number)"]
    statement := "*(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:455; source equation or documented promotion invariant"
    status := .proven, prop := ``P455, thm := some ``p455 },
  { id := "numberscov-promotion-s456", juliaFile := "base/promotion.jl"
    juliaFns := ["-(x::Number, y::Number)"]
    statement := "-(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:456; source equation or documented promotion invariant"
    status := .proven, prop := ``P456, thm := some ``p456 },
  { id := "numberscov-promotion-s457", juliaFile := "base/promotion.jl"
    juliaFns := ["/(x::Number, y::Number)"]
    statement := "/(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:457; source equation or documented promotion invariant"
    status := .proven, prop := ``P457, thm := some ``p457 },
  { id := "numberscov-promotion-s459", juliaFile := "base/promotion.jl"
    juliaFns := ["+%(x::Number, y::Number)"]
    statement := "+%(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:459; source equation or documented promotion invariant"
    status := .proven, prop := ``P459, thm := some ``p459 },
  { id := "numberscov-promotion-s460", juliaFile := "base/promotion.jl"
    juliaFns := ["*%(x::Number, y::Number)"]
    statement := "*%(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:460; source equation or documented promotion invariant"
    status := .proven, prop := ``P460, thm := some ``p460 },
  { id := "numberscov-promotion-s461", juliaFile := "base/promotion.jl"
    juliaFns := ["-%(x::Number, y::Number)"]
    statement := "-%(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:461; source equation or documented promotion invariant"
    status := .proven, prop := ``P461, thm := some ``p461 },
  { id := "numberscov-promotion-s507", juliaFile := "base/promotion.jl"
    juliaFns := ["^(x::Number, y::Number)"]
    statement := "^(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:507; source equation or documented promotion invariant"
    status := .proven, prop := ``P507, thm := some ``p507 },
  { id := "numberscov-promotion-s509", juliaFile := "base/promotion.jl"
    juliaFns := ["fma(x::Number, y::Number, z::Number)"]
    statement := "fma(x::Number, y::Number, z::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:509; source equation or documented promotion invariant"
    status := .proven, prop := ``P509, thm := some ``p509 },
  { id := "numberscov-promotion-s510", juliaFile := "base/promotion.jl"
    juliaFns := ["muladd(a::Number, b::Number, c::Number)"]
    statement := "muladd(a::Number, b::Number, c::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:510-514; source equation or documented promotion invariant"
    status := .proven, prop := ``P510, thm := some ``p510 },
  { id := "numberscov-promotion-s516", juliaFile := "base/promotion.jl"
    juliaFns := ["==(x::Number, y::Number)"]
    statement := "==(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:516; source equation or documented promotion invariant"
    status := .proven, prop := ``P516, thm := some ``p516 },
  { id := "numberscov-promotion-s517", juliaFile := "base/promotion.jl"
    juliaFns := ["<( x::Real, y::Real)"]
    statement := "<( x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:517; source equation or documented promotion invariant"
    status := .proven, prop := ``P517, thm := some ``p517 },
  { id := "numberscov-promotion-s518", juliaFile := "base/promotion.jl"
    juliaFns := ["<=(x::Real, y::Real)"]
    statement := "<=(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:518; source equation or documented promotion invariant"
    status := .proven, prop := ``P518, thm := some ``p518 },
  { id := "numberscov-promotion-s520", juliaFile := "base/promotion.jl"
    juliaFns := ["rem(x::Real, y::Real)"]
    statement := "rem(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:520; source equation or documented promotion invariant"
    status := .proven, prop := ``P520, thm := some ``p520 },
  { id := "numberscov-promotion-s521", juliaFile := "base/promotion.jl"
    juliaFns := ["mod(x::Real, y::Real)"]
    statement := "mod(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:521; source equation or documented promotion invariant"
    status := .proven, prop := ``P521, thm := some ``p521 },
  { id := "numberscov-promotion-s522", juliaFile := "base/promotion.jl"
    juliaFns := ["mod1(x::Real, y::Real)"]
    statement := "mod1(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:522; source equation or documented promotion invariant"
    status := .proven, prop := ``P522, thm := some ``p522 },
  { id := "numberscov-promotion-s523", juliaFile := "base/promotion.jl"
    juliaFns := ["fld1(x::Real, y::Real)"]
    statement := "fld1(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:523; source equation or documented promotion invariant"
    status := .proven, prop := ``P523, thm := some ``p523 },
  { id := "numberscov-promotion-s525", juliaFile := "base/promotion.jl"
    juliaFns := ["max(x::Real, y::Real)"]
    statement := "max(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:525; source equation or documented promotion invariant"
    status := .proven, prop := ``P525, thm := some ``p525 },
  { id := "numberscov-promotion-s526", juliaFile := "base/promotion.jl"
    juliaFns := ["min(x::Real, y::Real)"]
    statement := "min(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:526; source equation or documented promotion invariant"
    status := .proven, prop := ``P526, thm := some ``p526 },
  { id := "numberscov-promotion-s527", juliaFile := "base/promotion.jl"
    juliaFns := ["minmax(x::Real, y::Real)"]
    statement := "minmax(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:527; source equation or documented promotion invariant"
    status := .proven, prop := ``P527, thm := some ``p527 },
  { id := "numberscov-promotion-s529", juliaFile := "base/promotion.jl"
    juliaFns := ["TupleOrBottom(tt...)"]
    statement := "TupleOrBottom(tt...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:529-532; source equation or documented promotion invariant"
    status := .proven, prop := ``P529, thm := some ``p529 },
  { id := "numberscov-promotion-s641", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_op(f, S::Type...)"]
    statement := "promote_op(f, S::Type...) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:641-645; source equation or documented promotion invariant"
    status := .proven, prop := ``P641, thm := some ``p641 },
  { id := "numberscov-promotion-s650", juliaFile := "base/promotion.jl"
    juliaFns := ["no_op_err(name, T)"]
    statement := "no_op_err(name, T) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:650; source equation or documented promotion invariant"
    status := .proven, prop := ``P650, thm := some ``p650 },
  { id := "numberscov-promotion-s651", juliaFile := "base/promotion.jl"
    juliaFns := ["(+)(x::T, y::T) where {T<:Number}"]
    statement := "(+)(x::T, y::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:651; source equation or documented promotion invariant"
    status := .proven, prop := ``P651, thm := some ``p651 },
  { id := "numberscov-promotion-s652", juliaFile := "base/promotion.jl"
    juliaFns := ["(*)(x::T, y::T) where {T<:Number}"]
    statement := "(*)(x::T, y::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:652; source equation or documented promotion invariant"
    status := .proven, prop := ``P652, thm := some ``p652 },
  { id := "numberscov-promotion-s653", juliaFile := "base/promotion.jl"
    juliaFns := ["(-)(x::T, y::T) where {T<:Number}"]
    statement := "(-)(x::T, y::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:653; source equation or documented promotion invariant"
    status := .proven, prop := ``P653, thm := some ``p653 },
  { id := "numberscov-promotion-s654", juliaFile := "base/promotion.jl"
    juliaFns := ["(/)(x::T, y::T) where {T<:Number}"]
    statement := "(/)(x::T, y::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:654; source equation or documented promotion invariant"
    status := .proven, prop := ``P654, thm := some ``p654 },
  { id := "numberscov-promotion-s655", juliaFile := "base/promotion.jl"
    juliaFns := ["(^)(x::T, y::T) where {T<:Number}"]
    statement := "(^)(x::T, y::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:655; source equation or documented promotion invariant"
    status := .proven, prop := ``P655, thm := some ``p655 },
  { id := "numberscov-promotion-s657", juliaFile := "base/promotion.jl"
    juliaFns := ["fma(x::T, y::T, z::T) where {T<:Number}"]
    statement := "fma(x::T, y::T, z::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:657; source equation or documented promotion invariant"
    status := .proven, prop := ``P657, thm := some ``p657 },
  { id := "numberscov-promotion-s658", juliaFile := "base/promotion.jl"
    juliaFns := ["fma(x::Integer, y::Integer, z::Integer)"]
    statement := "fma(x::Integer, y::Integer, z::Integer) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:658; source equation or documented promotion invariant"
    status := .proven, prop := ``P658, thm := some ``p658 },
  { id := "numberscov-promotion-s659", juliaFile := "base/promotion.jl"
    juliaFns := ["muladd(x::T, y::T, z::T) where {T<:Number}"]
    statement := "muladd(x::T, y::T, z::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:659; source equation or documented promotion invariant"
    status := .proven, prop := ``P659, thm := some ``p659 },
  { id := "numberscov-promotion-s661", juliaFile := "base/promotion.jl"
    juliaFns := ["(&)(x::T, y::T) where {T<:Integer}"]
    statement := "(&)(x::T, y::T) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:661; source equation or documented promotion invariant"
    status := .proven, prop := ``P661, thm := some ``p661 },
  { id := "numberscov-promotion-s662", juliaFile := "base/promotion.jl"
    juliaFns := ["(|)(x::T, y::T) where {T<:Integer}"]
    statement := "(|)(x::T, y::T) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:662; source equation or documented promotion invariant"
    status := .proven, prop := ``P662, thm := some ``p662 },
  { id := "numberscov-promotion-s663", juliaFile := "base/promotion.jl"
    juliaFns := ["xor(x::T, y::T) where {T<:Integer}"]
    statement := "xor(x::T, y::T) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:663; source equation or documented promotion invariant"
    status := .proven, prop := ``P663, thm := some ``p663 },
  { id := "numberscov-promotion-s665", juliaFile := "base/promotion.jl"
    juliaFns := ["(==)(x::T, y::T) where {T<:Number}"]
    statement := "(==)(x::T, y::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:665; source equation or documented promotion invariant"
    status := .proven, prop := ``P665, thm := some ``p665 },
  { id := "numberscov-promotion-s666", juliaFile := "base/promotion.jl"
    juliaFns := ["(< )(x::T, y::T) where {T<:Real}"]
    statement := "(< )(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:666; source equation or documented promotion invariant"
    status := .proven, prop := ``P666, thm := some ``p666 },
  { id := "numberscov-promotion-s667", juliaFile := "base/promotion.jl"
    juliaFns := ["(<=)(x::T, y::T) where {T<:Real}"]
    statement := "(<=)(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:667; source equation or documented promotion invariant"
    status := .proven, prop := ``P667, thm := some ``p667 },
  { id := "numberscov-promotion-s669", juliaFile := "base/promotion.jl"
    juliaFns := ["rem(x::T, y::T) where {T<:Real}"]
    statement := "rem(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:669; source equation or documented promotion invariant"
    status := .proven, prop := ``P669, thm := some ``p669 },
  { id := "numberscov-promotion-s670", juliaFile := "base/promotion.jl"
    juliaFns := ["mod(x::T, y::T) where {T<:Real}"]
    statement := "mod(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:670; source equation or documented promotion invariant"
    status := .proven, prop := ``P670, thm := some ``p670 },
  { id := "numberscov-promotion-s672", juliaFile := "base/promotion.jl"
    juliaFns := ["min(x::Real)"]
    statement := "min(x::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:672; source equation or documented promotion invariant"
    status := .proven, prop := ``P672, thm := some ``p672 },
  { id := "numberscov-promotion-s673", juliaFile := "base/promotion.jl"
    juliaFns := ["max(x::Real)"]
    statement := "max(x::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:673; source equation or documented promotion invariant"
    status := .proven, prop := ``P673, thm := some ``p673 },
  { id := "numberscov-promotion-s674", juliaFile := "base/promotion.jl"
    juliaFns := ["minmax(x::Real)"]
    statement := "minmax(x::Real) follows its Julia source body for every allowed input."
    source := "base/promotion.jl:674; source equation or documented promotion invariant"
    status := .proven, prop := ``P674, thm := some ``p674 },
  { id := "numberscov-promotion-s676", juliaFile := "base/promotion.jl"
    juliaFns := ["max(x::T, y::T) where {T<:Real}"]
    statement := "max(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:676; source equation or documented promotion invariant"
    status := .proven, prop := ``P676, thm := some ``p676 },
  { id := "numberscov-promotion-s677", juliaFile := "base/promotion.jl"
    juliaFns := ["min(x::T, y::T) where {T<:Real}"]
    statement := "min(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:677; source equation or documented promotion invariant"
    status := .proven, prop := ``P677, thm := some ``p677 },
  { id := "numberscov-promotion-s678", juliaFile := "base/promotion.jl"
    juliaFns := ["minmax(x::T, y::T) where {T<:Real}"]
    statement := "minmax(x::T, y::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:678; source equation or documented promotion invariant"
    status := .proven, prop := ``P678, thm := some ``p678 },
  { id := "numberscov-promotion-s680", juliaFile := "base/promotion.jl"
    juliaFns := ["flipsign(x::T, y::T) where {T<:Signed}"]
    statement := "flipsign(x::T, y::T) where {T<:Signed} follows its Julia source body for every allowed input."
    source := "base/promotion.jl:680; source equation or documented promotion invariant"
    status := .proven, prop := ``P680, thm := some ``p680 }
]

end JuliaLean.NumbersCov.Rows.Promotion
