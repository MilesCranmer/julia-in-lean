import JuliaLean.Registry.Types
import JuliaLean.ErrorShow.ArrayshowFaithful

namespace JuliaLean.ErrorShow.ArrayshowEntries

open JuliaLean.Registry
open JuliaLean.ErrorShow.ArrayshowFaithful

def entries : List Entry := [
  { id := "errorshow-arrayshow-l42", juliaFile := "base/arrayshow.jl", juliaFns := ["replace_with_centered_mark"]
    statement := "Centered-mark replacement returns the marker at width zero or replaces the middle of exactly width spaces."
    source := "base/arrayshow.jl:42-45", status := .proven, prop := ``CenteredMarkExact, thm := some ``centeredMarkExact },
  { id := "errorshow-arrayshow-l60", juliaFile := "base/arrayshow.jl", juliaFns := ["alignment"]
    statement := "alignment computes each column maximum in row order, removes the first over-width column, and applies the narrow-width pruning branch."
    source := "base/arrayshow.jl:60-88", status := .proven, prop := ``AlignmentExact, thm := some ``alignmentExact },
  { id := "errorshow-arrayshow-l97", juliaFile := "base/arrayshow.jl", juliaFns := ["print_matrix_row"]
    statement := "print_matrix_row renders assigned or undef cells and applies exact left and right column padding with separators."
    source := "base/arrayshow.jl:97-124", status := .proven, prop := ``PrintMatrixRowExact, thm := some ``printMatrixRowExact },
  { id := "errorshow-arrayshow-l132", juliaFile := "base/arrayshow.jl", juliaFns := ["print_matrix_vdots"]
    statement := "print_matrix_vdots selects markers by modulus and residue and pads every selected or blank column with the source final-column exception."
    source := "base/arrayshow.jl:132-148", status := .proven, prop := ``PrintMatrixVdotsExact, thm := some ``printMatrixVdotsExact },
  { id := "errorshow-arrayshow-l163", juliaFile := "base/arrayshow.jl", juliaFns := ["print_matrix"]
    statement := "print_matrix forwards dimensions, limits, and full axes to the matrix planning body without changing its result."
    source := "base/arrayshow.jl:163-172", status := .proven, prop := ``PrintMatrixExact, thm := some ``printMatrixExact },
  { id := "errorshow-arrayshow-l174", juliaFile := "base/arrayshow.jl", juliaFns := ["_print_matrix"]
    statement := "_print_matrix selects the source front and back row and column counts and the corresponding vertical and horizontal ellipsis branches."
    source := "base/arrayshow.jl:174-273", status := .proven, prop := ``PrintMatrixPlanExact, thm := some ``printMatrixPlanExact },
  { id := "errorshow-arrayshow-l277", juliaFile := "base/arrayshow.jl", juliaFns := ["show_nd"]
    statement := "show_nd delegates the supplied axes and full-display flag to the higher-dimensional core."
    source := "base/arrayshow.jl:277-278", status := .proven, prop := ``ShowNdWrapperExact, thm := some ``showNdWrapperExact },
  { id := "errorshow-arrayshow-l280", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_nd"]
    statement := "_show_nd omits exactly middle indices of long limited axes and retains every allowed slice."
    source := "base/arrayshow.jl:280-349", status := .proven, prop := ``ShowNdCoreExact, thm := some ``showNdCoreExact },
  { id := "errorshow-arrayshow-l351", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_nd_label"]
    statement := "_show_nd_label emits the fixed leading dimensions, every tail index, closing bracket, equals sign, and newline."
    source := "base/arrayshow.jl:351-357", status := .proven, prop := ``ShowNdLabelExact, thm := some ``showNdLabelExact },
  { id := "errorshow-arrayshow-l364", juliaFile := "base/arrayshow.jl", juliaFns := ["print_array(::AbstractArray{T,0})"]
    statement := "Zero-dimensional print_array shows its sole assigned element or the undef marker."
    source := "base/arrayshow.jl:364-365", status := .proven, prop := ``PrintArrayZeroExact, thm := some ``printArrayZeroExact },
  { id := "errorshow-arrayshow-l366", juliaFile := "base/arrayshow.jl", juliaFns := ["print_array(::AbstractVecOrMat)"]
    statement := "Vector-or-matrix print_array delegates all dimensions and limit state to print_matrix."
    source := "base/arrayshow.jl:366", status := .proven, prop := ``PrintArrayVecOrMatExact, thm := some ``printArrayVecOrMatExact },
  { id := "errorshow-arrayshow-l367", juliaFile := "base/arrayshow.jl", juliaFns := ["print_array(::AbstractArray)"]
    statement := "Higher-dimensional print_array delegates every slice to full show_nd."
    source := "base/arrayshow.jl:367", status := .proven, prop := ``PrintArrayHigherExact, thm := some ``printArrayHigherExact },
  { id := "errorshow-arrayshow-l371", juliaFile := "base/arrayshow.jl", juliaFns := ["show(::MIME\"text/plain\",::AbstractArray)"]
    statement := "Plain array show takes the exact two-argument, summary-only, one-line, or content branch from emptiness, compactness, rank, size, limit, and display height."
    source := "base/arrayshow.jl:371-414", status := .proven, prop := ``ShowArrayPlainRouteExact, thm := some ``showArrayPlainRouteExact },
  { id := "errorshow-arrayshow-l416", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_oneline_truncated"]
    statement := "One-line array truncation subtracts summary width and two characters and enforces the source minimum width of eight."
    source := "base/arrayshow.jl:416-423", status := .proven, prop := ``ShowOnelineWidthExact, thm := some ``showOnelineWidthExact },
  { id := "errorshow-arrayshow-l436", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_nonempty(::AbstractMatrix,prefix)"]
    statement := "The matrix wrapper delegates its axes and limit state to the full nonempty-matrix method."
    source := "base/arrayshow.jl:436-437", status := .proven, prop := ``ShowNonemptyMatrixWrapperExact, thm := some ``showNonemptyMatrixWrapperExact },
  { id := "errorshow-arrayshow-l439", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_nonempty(::AbstractMatrix,...)"]
    statement := "Nonempty matrix literal output selects all rows and columns or the first and last two with ellipses exactly at the four-element limit."
    source := "base/arrayshow.jl:439-485", status := .proven, prop := ``ShowNonemptyMatrixExact, thm := some ``showNonemptyMatrixExact },
  { id := "errorshow-arrayshow-l488", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_nonempty(::AbstractArray,prefix)"]
    statement := "Higher-dimensional nonempty output prints its prefix and then the literal show_nd output."
    source := "base/arrayshow.jl:488-491", status := .proven, prop := ``ShowNonemptyHigherExact, thm := some ``showNonemptyHigherExact },
  { id := "errorshow-arrayshow-l494", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_nonempty(::AbstractVector,...)"]
    statement := "The forbidden vector overload always raises its fixed not-implemented error."
    source := "base/arrayshow.jl:494-495", status := .proven, prop := ``ShowNonemptyVectorExact, thm := some ``showNonemptyVectorExact },
  { id := "errorshow-arrayshow-l497", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_nonempty(::AbstractArray{T,0},prefix)"]
    statement := "The zero-dimensional nonempty overload delegates exactly to print_array."
    source := "base/arrayshow.jl:497", status := .proven, prop := ``ShowNonemptyZeroExact, thm := some ``showNonemptyZeroExact },
  { id := "errorshow-arrayshow-l500", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_empty(::Array)"]
    statement := "Empty concrete Array output prints its type, undef, comma-separated dimensions, and closing parenthesis."
    source := "base/arrayshow.jl:500-503", status := .proven, prop := ``ShowEmptyArrayExact, thm := some ``showEmptyArrayExact },
  { id := "errorshow-arrayshow-l504", juliaFile := "base/arrayshow.jl", juliaFns := ["_show_empty(::AbstractArray)"]
    statement := "Empty abstract-array output returns exactly summary(io,X)."
    source := "base/arrayshow.jl:504", status := .proven, prop := ``ShowEmptyAbstractExact, thm := some ``showEmptyAbstractExact },
  { id := "errorshow-arrayshow-l507", juliaFile := "base/arrayshow.jl", juliaFns := ["show(::AbstractArray)"]
    statement := "Two-argument array show dispatches by rank, emptiness, circularity, and nonempty content in source order."
    source := "base/arrayshow.jl:507-520", status := .proven, prop := ``ShowArrayRouteExact, thm := some ``showArrayRouteExact },
  { id := "errorshow-arrayshow-l523", juliaFile := "base/arrayshow.jl", juliaFns := ["show_zero_dim(::BitArray{0})"]
    statement := "Zero-dimensional BitArray show prints BitArray around its integer Boolean value."
    source := "base/arrayshow.jl:523", status := .proven, prop := ``ShowZeroBitExact, thm := some ``showZeroBitExact },
  { id := "errorshow-arrayshow-l524", juliaFile := "base/arrayshow.jl", juliaFns := ["show_zero_dim(::AbstractArray{T,0})"]
    statement := "Zero-dimensional array show emits fill(value) when assigned and Array{T,0}(undef) otherwise."
    source := "base/arrayshow.jl:524-533", status := .proven, prop := ``ShowZeroArrayExact, thm := some ``showZeroArrayExact },
  { id := "errorshow-arrayshow-l540", juliaFile := "base/arrayshow.jl", juliaFns := ["show_vector"]
    statement := "show_vector emits all items unless limited length exceeds twenty, then first ten, one ellipsis, and last ten."
    source := "base/arrayshow.jl:540-558", status := .proven, prop := ``ShowVectorExact, thm := some ``showVectorExact },
  { id := "errorshow-arrayshow-l568", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_eltype(::Any)"]
    statement := "The generic typeinfo_eltype fallback returns nothing for every input."
    source := "base/arrayshow.jl:568", status := .proven, prop := ``TypeinfoEltypeFallbackExact, thm := some ``typeinfoEltypeFallbackExact },
  { id := "errorshow-arrayshow-l569", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_eltype(::Type{Union{}})"]
    statement := "The one-argument Bottom typeinfo_eltype method returns nothing."
    source := "base/arrayshow.jl:569", status := .proven, prop := ``TypeinfoEltypeBottomExact, thm := some ``typeinfoEltypeBottomExact },
  { id := "errorshow-arrayshow-l570", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_eltype(::Type{Union{}},slurp...)"]
    statement := "The variadic Bottom typeinfo_eltype method always raises MethodError."
    source := "base/arrayshow.jl:570", status := .proven, prop := ``TypeinfoBottomSlurpExact, thm := some ``typeinfoBottomSlurpExact },
  { id := "errorshow-arrayshow-l571", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_eltype(::Type{<:AbstractArray})"]
    statement := "Array typeinfo_eltype returns exactly its element type."
    source := "base/arrayshow.jl:571", status := .proven, prop := ``TypeinfoArrayExact, thm := some ``typeinfoArrayExact },
  { id := "errorshow-arrayshow-l572", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_eltype(::Type{<:AbstractDict})"]
    statement := "Dictionary typeinfo_eltype returns Pair{K,V}."
    source := "base/arrayshow.jl:572", status := .proven, prop := ``TypeinfoDictExact, thm := some ``typeinfoDictExact },
  { id := "errorshow-arrayshow-l573", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_eltype(::Type{<:AbstractSet})"]
    statement := "Set typeinfo_eltype returns exactly its element type."
    source := "base/arrayshow.jl:573", status := .proven, prop := ``TypeinfoSetExact, thm := some ``typeinfoSetExact },
  { id := "errorshow-arrayshow-l580", juliaFile := "base/arrayshow.jl", juliaFns := ["_typeinfo_implicit"]
    statement := "_typeinfo_implicit returns exactly the invoke_in_world result for the current world."
    source := "base/arrayshow.jl:580", status := .proven, prop := ``TypeinfoImplicitInvokeExact, thm := some ``typeinfoImplicitInvokeExact },
  { id := "errorshow-arrayshow-l583", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_implicit"]
    statement := "typeinfo_implicit is true exactly for singleton, kind, type-variable, or union types."
    source := "base/arrayshow.jl:583-592", status := .proven, prop := ``TypeinfoImplicitExact, thm := some ``typeinfoImplicitExact },
  { id := "errorshow-arrayshow-l595", juliaFile := "base/arrayshow.jl", juliaFns := ["typeinfo_prefix"]
    statement := "typeinfo_prefix selects implicit output, explicit array type, or explicit element type in the source branch order."
    source := "base/arrayshow.jl:595-626", status := .proven, prop := ``TypeinfoPrefixExact, thm := some ``typeinfoPrefixExact }
]

end JuliaLean.ErrorShow.ArrayshowEntries
