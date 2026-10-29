import JuliaLean.base.broadcast
import JuliaLean.Registry.Types
import JuliaLean.base.operators
import JuliaLean.base.range
import JuliaLean.base.multidimensional

/-!
# Specifications of `base/broadcast.jl`

Shape compatibility, elementwise application, and in-place storage behavior.
The retained refutations concern the source-facing definitions in the new model.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
namespace JuliaLean.Proofs.base.broadcast
open JuliaLean JuliaLean.base.broadcast

/-! Nothing to promise:
combine_styles@429: empty generic declaration, with no executable method body.
result_style@456: empty generic declaration, with no executable method body.
broadcast_shape@519: empty generic declaration, with no executable method body.
-/

/-! Nothing to promise:
BroadcastStyle@37: ambiguity-resolution method returning a zero-field dispatch marker.
BroadcastStyle@49: tuple dispatch marker; the result type is selected by trusted Julia dispatch.
ArrayStyle@87: zero-field constructor forwarding; ArrayStyle carries no dimension value.
DefaultArrayStyle@98: Val-to-type-parameter constructor forwarding.
BroadcastStyle@102: array-type-to-trait forwarding; there is no array computation.
BroadcastStyle@103: forwards the external ndims type query into a zero-field trait constructor.
ArrayConflict@111: Val constructor discards its argument and returns the zero-field conflict marker.
BroadcastStyle@128: forwards to the zero-argument constructor of the dispatch-selected homogeneous style.
BroadcastStyle@130: fallback dispatch marker used to request argument swapping.
BroadcastStyle@132: ambiguity-resolution marker for two Unknown arguments.
BroadcastStyle@133: forwards to the zero-argument constructor of the non-Unknown style.
BroadcastStyle@135: returns the tuple input unchanged; precedence is selected by trusted dispatch.
BroadcastStyle@136: returns the array-style input unchanged; precedence is selected by trusted dispatch.
BroadcastStyle@137: forwards to the zero-argument constructor of the dispatch-selected ArrayStyle type.
BroadcastStyle@138: marker for unresolved distinct ArrayStyle types; no element or dimension computation.
BroadcastStyle@139: forwards to the zero-argument constructor of the dispatch-selected AbstractArrayStyle type.
BroadcastStyle@147: returns the non-default style unchanged, with no computation.
BroadcastStyle@148: returns the equal-rank non-default style unchanged, with no computation.
Broadcasted@175: tuple-function ambiguity guard; no callable or container computation.
Broadcasted@181: forwards style discovery into the explicit-style wrapper constructor.
Broadcasted@185: stores supplied fields after the style constructor's type assertion.
Broadcasted@189: forwards runtime field conversions into wrapper storage; conversion laws belong to Core.new.
broadcasted(::AndAnd)@196: forwards ordinary scalar Boolean conjunction to generic broadcasted.
broadcasted(::OrOr)@207: forwards ordinary scalar Boolean disjunction to generic broadcasted.
convert(::Type{Broadcasted}, ::Broadcasted)@215: rewraps the same function, argument tuple, and axes under the requested style.
similar(::Broadcasted, ::Type)@229: forwards to the explicit-axes similar overload.
similar(::Broadcasted{DefaultArrayStyle}, ::Type{Bool}, dims)@232: forwards the supplied axes to the external BitArray allocator.
similar(::Broadcasted{ArrayConflict}, ::Type{Bool}, dims)@237: forwards the supplied axes to the external BitArray allocator.
_axes(::Broadcasted{AbstractArrayStyle{0}}, ::Nothing)@243: zero-rank dispatch plumbing returning the empty axis tuple.
BroadcastStyle(::Type{<:Broadcasted})@248: forwards to the style type's zero-argument constructor.
BroadcastStyle(::Type{<:Broadcasted{Nothing}})@249: unassigned-style ambiguity guard, with no container computation.
argtype(::Broadcasted)@253: forwards the typeof query to the type-level argtype accessor.
eachindex(::Broadcasted)@255: forwards to the index-style-specific eachindex overload.
eachindex(::IndexStyle, ::Broadcasted)@256: forwards the wrapper axes to the external index constructor.
eachindex(::IndexCartesian, axes)@257: forwards axes into the external CartesianIndices constructor.
eachindex(::IndexLinear, axes)@258: forwards LinearIndices into its eachindex overload.
eachindex(::IndexLinear, ::Tuple{Any})@259: returns the sole supplied axis unchanged.
IndexStyle(::Broadcasted)@261: forwards to the type-level index trait.
IndexStyle(::Type{<:Broadcasted{AbstractArrayStyle{0}}})@262: zero-rank linear-index dispatch marker.
IndexStyle(::Type{<:Broadcasted})@263: fallback Cartesian-index dispatch marker.
eachindex(::Broadcasted{AbstractArrayStyle{0}})@265: forwards axes into the external LinearIndices constructor.
ndims(::Broadcasted)@267: forwards to the type-level dimensionality query.
ndims(::Type{<:Broadcasted{NTuple{N}}})@268: forwards the static tuple rank parameter.
length(::Broadcasted)@282: forwards the source size query to the external prod implementation.
iterate(::Broadcasted)@284: forwards the external index iterator into the real wrapper-step method.
iterate(::Broadcasted, state)@288: iterator-protocol adapter transporting the external cursor and forwarded element unchanged.
IteratorSize(::Type{<:Broadcasted})@295: forwards ndims into the external HasShape trait constructor.
IteratorEltype(::Type{<:Broadcasted})@296: external iteration-eltype trait marker.
instantiate(x)@299: identity forwarding for non-wrapper values.
instantiate(::Broadcasted{AbstractArrayStyle{0}})@319: dispatch-selected identity forwarding.
instantiate(::Broadcasted{Style{Tuple},Nothing})@321: dispatch-selected identity forwarding.
check_broadcast_shape(shp)@548: no source axes were supplied, so there is no constraint to check.
check_broadcast_shape(shp, ::Tuple{})@549: an empty source axes tuple contributes no constraints.
check_broadcast_shape(::Tuple{}, ::Tuple{})@550: ambiguity resolution for two empty tuples.
combine_styles()@431: zero-argument dispatch marker for scalar output.
combine_styles(c)@432: forwards the external type query to unary result_style.
combine_styles(::Broadcasted)@433: assigned-style accessor with an unassigned-style guard.
combine_styles(c1,c2)@437: forwards the two discovered traits to binary result_style.
combine_styles(c1,c2,cs...)@438: recursively forwards argument traits to result_style; the binary methods supply the selection policy.
result_style(::BroadcastStyle)@458: identity forwarding for one style.
result_style(s1,s2)@463: forwards the two directional rules to result_join; selection belongs to the join overloads.
result_join(::Any,::Any,::Unknown,::Unknown)@467: unresolved-style dispatch marker.
result_join(::Any,::Any,::Unknown,::BroadcastStyle)@468: returns the supplied resolved style unchanged.
result_join(::Any,::Any,::BroadcastStyle,::Unknown)@469: returns the supplied resolved style unchanged.
result_join(::AbstractArrayStyle,::AbstractArrayStyle,::Unknown,::Unknown)@474: array-conflict dispatch marker.
result_join(::S,::T,::U,::V)@479: conflicting-rule diagnostic guard, with no style-selection computation.
combine_axes(A,B...)@502: forwards recursively discovered axes to broadcast_shape; shape selection belongs to that function.
combine_axes(A,B)@503: forwards the two external axes queries to broadcast_shape.
broadcast_shape(::Tuple)@521: identity forwarding for a single supplied shape.
_bcs(::Tuple{},::Tuple{})@524: empty-tuple constructor base case.
axistype(::OneTo,::OneTo)@543: forwards the selected axis to the external OneTo{Int} constructor.
axistype(a,b)@544: forwards the selected axis to the external UnitRange{Int} constructor.
newindexer(A)@606: forwards the external axes query to the real shapeindexer.
getindex(::Broadcasted, Is...)@615: forwards externally flattened coordinates and the index-style query to the selected indexing method.
_getindex(::IndexCartesian,bc,::Integer)@623: forwards external CartesianIndices conversion into the selected indexing method.
_getindex(::IndexLinear,bc,::CartesianIndex)@627: forwards external LinearIndices conversion into the selected indexing method.
to_index(::Tuple{})@631: zero-coordinate CartesianIndex constructor.
to_index(::Tuple{Any})@632: forwards the sole tuple field unchanged.
to_index(::Tuple)@633: forwards tuple coordinates to the CartesianIndex constructor.
_broadcast_getindex(A,I)@657: forwards broadcast index remapping into external array indexing.
axes(::Extruded)@669: forwards the external axes query to the stored underlying array.
_broadcast_getindex(::Extruded,i)@670: forwards stored index-remapping metadata into external array indexing.
extrude(x)@672: identity forwarding for non-array inputs.
-/

/-!
## Source-order coverage

| Julia methods | Resolution | Count |
| --- | --- | ---: |
| Methods named by the source-facing entries below | Source-facing registered specifications | 80 |
| Methods named in the Nothing-to-promise block | Constructor, trait, or forwarding plumbing | 83 |
| Inherited candidates at lines 593, 1001, 1015, 1200, 1223, and 1236 | Require further subject and source review | 6 |
| Other methods, starting at line 594 | No settled source-facing specification | 169 |

The 338 numbered definitions contain no untranslated blocks. These are working counts, not an
independent certification of body fidelity or full coverage. Generic declarations at lines 429,
456, and 519 are counted separately. Integer and axis shape statements, coordinate projection,
and indexer flags use the real recursive numbered overloads. The retained integer shape
properties and eight range-method counterexample subjects have been repaired to source calls.
The next source-order target is the keep/default remapping family at lines 593-602.
-/

namespace StyleProofs
open Style

/-- The bottom-type ambiguity error identifies the called function and retains every supplied
argument, in its original position, after the leading bottom-type argument. -/
def BottomTypeDiagnostic : Prop :=
  ∀ {A : Type} (args : List A),
    ∃ failure, m38 args = .error failure ∧
      failure.functionName = "BroadcastStyle" ∧
      failure.arguments.length = args.length + 1 ∧
      failure.arguments[0]? = some .bottomType ∧
      ∀ i, failure.arguments[i + 1]? = (args[i]?).map MethodArgument.value

theorem bottomTypeDiagnostic : BottomTypeDiagnostic := by
  intro A args
  refine ⟨⟨"BroadcastStyle", .bottomType :: args.map .value⟩, rfl, rfl, ?_, rfl, ?_⟩
  · simp
  · intro i
    simp

/-- A rank-parameterized array family combines dimensions by their least upper bound.
For DefaultArrayStyle, both the same-family rule and the default-style fallback use the real
Val constructor. A correct join is an input rank and is at least both input ranks. -/
def DimensionJoin : Prop :=
  ∀ {E : Type} (maximum : Rank → Rank → Except E Rank),
    (∀ m n, maximum (.fixed m) (.fixed n) = .ok (.fixed (max m n))) →
    ∀ (sameTypename : Rank → Rank → Bool) (m n : Nat),
      sameTypename (.fixed m) (.fixed n) = true →
      ∀ k : Nat,
        ((m140 sameTypename maximum m99 (.fixed m) (.fixed n) (.fixed m) (.fixed n)).map Style.rank =
            .ok (.fixed k) ↔ m ≤ k ∧ n ≤ k ∧ (k = m ∨ k = n)) ∧
        ((m149 maximum m99 (.fixed m) (.fixed m) (.fixed n)).map Style.rank =
            .ok (.fixed k) ↔ m ≤ k ∧ n ≤ k ∧ (k = m ∨ k = n))

theorem dimensionJoin : DimensionJoin := by
  intro E maximum hmax sameTypename m n hs k
  simp [m140, hs, m149, hmax, m99, defaultStyle, bind, Except.bind, pure, Except.pure, Except.map]
  omega

/-- The dimension chosen for three default-array inputs is independent of parenthesization
and argument order. Each intermediate rank is reconstructed by the source Val constructor. -/
def DimensionJoinAssociative : Prop :=
  ∀ {E : Type} (maximum : Rank → Rank → Except E Rank),
    (∀ m n, maximum (.fixed m) (.fixed n) = .ok (.fixed (max m n))) →
    ∀ a b c : Nat,
      (do
        let left ← m149 maximum m99 (.fixed a) (.fixed a) (.fixed b)
        m149 maximum m99 left.rank left.rank (.fixed c)) =
      (do
        let right ← m149 maximum m99 (.fixed b) (.fixed b) (.fixed c)
        m149 maximum m99 (.fixed a) (.fixed a) right.rank) ∧
      m149 maximum m99 (.fixed a) (.fixed a) (.fixed b) =
        m149 maximum m99 (.fixed b) (.fixed b) (.fixed a)

theorem dimensionJoinAssociative : DimensionJoinAssociative := by
  intro E maximum hmax a b c
  simp [m149, hmax, m99, defaultStyle, bind, Except.bind, pure, Except.pure] <;> omega

/-- Rank comparison failures are preserved by both array-style join methods. In particular,
the broadcasting layer cannot turn a failed external max(Any, N) into a successful Any rank. -/
def DimensionJoinFailures : Prop :=
  ∀ {E : Type} (maximum : Rank → Rank → Except E Rank)
      (sameTypename : Rank → Rank → Bool) (a b rankA rankB : Rank) (error : E),
    sameTypename a b = true → maximum rankA rankB = .error error →
      m140 sameTypename maximum m99 a b rankA rankB = .error error ∧
      m149 maximum m99 a rankA rankB = .error error

theorem dimensionJoinFailures : DimensionJoinFailures := by
  intro E maximum sameTypename a b rankA rankB error hs he
  simp [m140, hs, m149, he, bind, Except.bind]

/-- Same-type styles agree exactly when they denote the identical style value. A successful
result preserves that value. The identity primitive's reflexivity and soundness are its
documented interface; both Julia-owned resolution methods are instantiated concretely. -/
def IdentityAgreement : Prop :=
  ∀ (identical : Style → Style → Bool),
    (∀ style, identical style style = true) →
    (∀ left right, identical left right = true → left = right) →
    ∀ {A B : Type} (left : A) (right : B) (forward reverse result : Style),
      (m459 identical forward reverse = .ok result ↔ forward = reverse ∧ result = forward) ∧
      (m477 identical left right forward reverse = .ok result ↔ forward = reverse ∧ result = forward)

theorem identityAgreement : IdentityAgreement := by
  intro identical hrefl hsound A B left right forward reverse result
  cases h : identical forward reverse with
  | false =>
    have hn : forward ≠ reverse := by
      intro he
      subst reverse
      rw [hrefl] at h
      cases h
    simp [m459, m477, h, hn]
  | true =>
    have he := hsound forward reverse h
    subst reverse
    simp [m459, m477, hrefl, eq_comm]
end StyleProofs

namespace WrapperProofs

/-- Display prints balanced wrapper punctuation and includes a style annotation exactly for
instantiated axes. The length formula counts the added punctuation independently of printing. -/
def DisplayPresentation : Prop :=
  ∀ {S F A X T : Type}
      (printHead : String → Except Lazy.Error String)
      (printStyle : String → T → Except Lazy.Error String)
      (printBody : String → F → A → Except Lazy.Error String)
      (styleType : Unit → T) (isTupleAxes : X → Bool)
      (header : String) (renderStyle : T → String) (renderF : F → String)
      (renderArgs : A → String),
    (∀ io, printHead io = .ok (io ++ header)) →
    (∀ io style, printStyle io style = .ok (io ++ "{" ++ renderStyle style ++ "}")) →
    (∀ io f args, printBody io f args = .ok (io ++ "(" ++ renderF f ++ ", " ++ renderArgs args ++ ")")) →
    ∀ io (bc : Lazy.Broadcasted S F A X),
      let decoration := if isTupleAxes bc.axes then "{" ++ renderStyle (styleType ()) ++ "}" else ""
      Lazy.m218 printHead printStyle printBody styleType isTupleAxes io bc =
        .ok (io ++ header ++ decoration ++ "(" ++ renderF bc.f ++ ", " ++ renderArgs bc.args ++ ")", ()) ∧
      ∀ result,
        Lazy.m218 printHead printStyle printBody styleType isTupleAxes io bc = .ok (result, ()) →
        result.length = io.length + header.length + decoration.length +
          (renderF bc.f).length + (renderArgs bc.args).length + 4

theorem displayPresentation : DisplayPresentation := by
  intro S F A X T printHead printStyle printBody styleType isTupleAxes header renderStyle
    renderF renderArgs hhead hstyle hbody io bc
  have lp : "(".length = 1 := by decide
  have comma : ", ".length = 2 := by decide
  have rp : ")".length = 1 := by decide
  have lb : "{".length = 1 := by decide
  have rb : "}".length = 1 := by decide
  have joined : "}(".length = 2 := by decide
  cases haxes : isTupleAxes bc.axes <;>
    simp [Lazy.m218, hhead, hstyle, hbody, haxes, bind, Except.bind,
      String.append_assoc, String.length_append, lp, comma, rp, lb, rb, joined] <;> omega

/-- Explicit output axes determine the number of size components, even when an argument's
axes query would fail or would report a different rank. -/
def StoredAxesRank : Prop :=
  ∀ {E S F A : Type} (length : Shape.Dim → Lazy.I64)
      (argumentAxes : A → Except E (List Shape.Dim))
      (bc : Lazy.Broadcasted S F A (Option (List Shape.Dim))) (supplied : List Shape.Dim),
    bc.axes = some supplied →
      (Lazy.m281 length (Lazy.m240 (Lazy.m242 (Shape.m504 argumentAxes))) bc).map List.length =
        .ok supplied.length

theorem storedAxesRank : StoredAxesRank := by
  intro E S F A length argumentAxes bc supplied hs
  simp [Lazy.m281, Lazy.m240, Lazy.m241, hs, bind, Except.bind, pure, Except.pure, Except.map]

/-- Valid axes have nonnegative lengths. Every successful size query inherits that invariant,
including inferred axes obtained through the actual single-argument combine_axes method. -/
def SizeExtentsNonnegative : Prop :=
  ∀ {E S F A : Type} (length : Shape.Dim → Lazy.I64)
      (argumentAxes : A → Except E (List Shape.Dim)),
    (∀ axis, 0 ≤ (length axis).val) →
    ∀ (bc : Lazy.Broadcasted S F A (Option (List Shape.Dim))) sizes,
      Lazy.m281 length (Lazy.m240 (Lazy.m242 (Shape.m504 argumentAxes))) bc = .ok sizes →
      ∀ extent ∈ sizes, 0 ≤ extent.val

theorem sizeExtentsNonnegative : SizeExtentsNonnegative := by
  intro E S F A length argumentAxes hlength bc sizes hsize
  cases ha : Lazy.m240 (Lazy.m242 (Shape.m504 argumentAxes)) bc with
  | error e =>
    simp [Lazy.m281, ha, bind, Except.bind] at hsize
  | ok axes =>
    simp [Lazy.m281, ha, bind, Except.bind, pure, Except.pure] at hsize
    subst sizes
    intro extent he
    obtain ⟨axis, _, rfl⟩ := List.mem_map.mp he
    exact hlength axis

/-- Dimensions beyond a wrapper's declared rank have singleton axes, irrespective of the
stored axes or any failing axes lookup. -/
def BeyondRankSingleton : Prop :=
  ∀ {S F A Axis : Type} (getindex : List Axis → Int → Except Lazy.Error Axis)
      (axisLength : Axis → Nat) (oneToOne : Axis),
    axisLength oneToOne = 1 →
    ∀ (bc : Lazy.Broadcasted S F A (Option (List Axis))) (rank d : Int),
      rank < d →
      (Lazy.m245 (Lazy.m240 Lazy.m243) getindex oneToOne bc rank d).map axisLength = .ok 1

theorem beyondRankSingleton : BeyondRankSingleton := by
  intro S F A Axis getindex axisLength oneToOne hlength bc rank d hd
  have hnot : ¬ d ≤ rank := by omega
  simp [Lazy.m245, hnot, hlength, Except.map]

/-- Default-array and conflict-style allocation derive their result rank from the supplied
axes, rather than a prior style rank. The allocated rank agrees with its stored axes. -/
def AllocatedRankMatchesAxes : Prop :=
  ∀ {E T Axis Out : Type} (allocate : T → Nat → List Axis → Except E Out)
      (rank : Out → Nat) (axes : Out → List Axis),
    (∀ elementType n dims result, allocate elementType n dims = .ok result →
      rank result = n ∧ axes result = dims) →
    ∀ elementType dims result,
      (Lazy.m230 allocate elementType dims = .ok result →
        rank result = (axes result).length ∧ axes result = dims) ∧
      (Lazy.m235 allocate elementType dims = .ok result →
        rank result = (axes result).length ∧ axes result = dims)

theorem allocatedRankMatchesAxes : AllocatedRankMatchesAxes := by
  intro E T Axis Out allocate rank axes hallocate elementType dims result
  constructor <;> intro hout
  all_goals
    obtain ⟨hrank, haxes⟩ := hallocate elementType dims.length dims result hout
    exact ⟨by rw [hrank, haxes], haxes⟩
end WrapperProofs

namespace RankProofs

theorem recursiveRank (head : Lazy.ArgRank) (tail : List Lazy.ArgRank) :
    Lazy.m275 head tail = max (Lazy.argRank head) (Lazy.maxNdim tail) := by
  rw [Lazy.m275.eq_def]
  rfl

theorem consRank (head : Lazy.ArgRank) (tail : List Lazy.ArgRank) :
    Lazy.maxNdim (head :: tail) = max (Lazy.argRank head) (Lazy.maxNdim tail) := by
  cases tail with
  | nil => simp [Lazy.maxNdim, Lazy.m273, Lazy.m274]
  | cons next rest => exact recursiveRank head (next :: rest)

theorem bound_iff (args : List Lazy.ArgRank) (bound : Nat) :
    Lazy.maxNdim args ≤ bound ↔ ∀ arg ∈ args, Lazy.argRank arg ≤ bound := by
  induction args with
  | nil => simp [Lazy.maxNdim, Lazy.m273]
  | cons head tail ih =>
    rw [consRank]
    constructor
    · intro h arg hm
      rcases List.mem_cons.mp hm with rfl | hm
      · have := Nat.le_max_left (Lazy.argRank arg) (Lazy.maxNdim tail)
        omega
      · apply ih.mp
        · have := Nat.le_max_right (Lazy.argRank head) (Lazy.maxNdim tail)
          omega
        · exact hm
    · intro h
      have hh := h head (by simp)
      have ht : Lazy.maxNdim tail ≤ bound := ih.mpr (fun arg hm => h arg (by simp [hm]))
      omega

/-- The inferred dimensionality is the least upper bound of the argument dimensionalities,
with tuples contributing one dimension and an empty argument tuple contributing zero. -/
def InferredRankLeast : Prop :=
  ∀ (bcType : Lazy.BroadcastedType (List Lazy.ArgRank)) (bound : Nat),
    Lazy.m269 bcType ≤ bound ↔ ∀ arg ∈ bcType.argsType, Lazy.argRank arg ≤ bound

theorem inferredRankLeast : InferredRankLeast := by
  intro bcType bound
  exact bound_iff bcType.argsType bound

/-- An array style that does not encode a fixed rank obtains exactly the same least upper
bound from its arguments, using the source argtype query and _maxndims methods. -/
def UnfixedStyleRankLeast : Prop :=
  ∀ (bcType : Lazy.BroadcastedType (List Lazy.ArgRank)),
    bcType.styleRank = .any → ∀ bound : Nat,
      Lazy.m270 bcType ≤ bound ↔ ∀ arg ∈ bcType.argsType, Lazy.argRank arg ≤ bound

theorem unfixedStyleRankLeast : UnfixedStyleRankLeast := by
  intro bcType hs bound
  simpa [Lazy.m270, Lazy.m252, hs] using bound_iff bcType.argsType bound

/-- Permuting broadcast arguments cannot change the inferred number of result dimensions. -/
def RankPermutationInvariant : Prop :=
  ∀ (left right : Lazy.BroadcastedType (List Lazy.ArgRank)),
    left.argsType.Perm right.argsType → Lazy.m269 left = Lazy.m269 right

theorem rankPermutationInvariant : RankPermutationInvariant := by
  intro left right hp
  apply Nat.le_antisymm
  · apply (inferredRankLeast left (Lazy.m269 right)).mpr
    intro arg hm
    exact (inferredRankLeast right (Lazy.m269 right)).mp (Nat.le_refl _) arg (hp.mem_iff.mp hm)
  · apply (inferredRankLeast right (Lazy.m269 left)).mpr
    intro arg hm
    exact (inferredRankLeast left (Lazy.m269 left)).mp (Nat.le_refl _) arg (hp.mem_iff.mpr hm)
end RankProofs

namespace ValidationProofs

theorem emptyShape {D Axis : Type} {t : IntTy} (equal : D → Axis → Bool)
    (length : Axis → JInt t) (axes : List Axis) :
    Shape.checkShape equal length [] axes = Shape.m551 length axes := by
  cases axes <;> rfl

theorem shapeCons {D Axis : Type} {t : IntTy} (equal : D → Axis → Bool)
    (length : Axis → JInt t) (head : D) (tail : List D) (axis : Axis) (axes : List Axis) :
    Shape.checkShape equal length (head :: tail) (axis :: axes) =
      if !Shape.m536 equal length head axis then .error .dimensionMismatch
      else Shape.checkShape equal length tail axes := by
  change Shape.m557 equal length head tail axis axes = _
  rw [Shape.m557.eq_def]
  cases tail <;> cases axes <;> rfl

theorem omittedAxesSingleton {D Axis : Type} {t : IntTy} (equal : D → Axis → Bool)
    (length : Axis → JInt t) (shape : List D) (axes : List Axis)
    (h : Shape.checkShape equal length shape axes = .ok ()) :
    ∀ axis ∈ axes.drop shape.length, (length axis).val = 1 := by
  induction shape generalizing axes with
  | nil =>
    rw [emptyShape] at h
    simp only [List.length_nil, List.drop_zero]
    simpa [Shape.m551] using h
  | cons head tail ih =>
    cases axes with
    | nil => simp
    | cons axis rest =>
      rw [shapeCons] at h
      split at h
      · cases h
      · simpa using ih rest h

/-- Checking a destination shape cannot silently discard a varying source dimension. Every
source axis beyond the destination rank must be a singleton. -/
def ValidationPreservesVaryingAxes : Prop :=
  ∀ {A D Axis : Type} {t : IntTy} (axes : A → Shape.Result (List Axis))
      (equal : D → Axis → Bool) (length : Axis → JInt t)
      (shape : List D) (array : A) (sourceAxes : List Axis),
    axes array = .ok sourceAxes →
    Shape.m561 axes equal length shape array = .ok () →
      ∀ axis ∈ sourceAxes.drop shape.length, (length axis).val = 1

theorem validationPreservesVaryingAxes : ValidationPreservesVaryingAxes := by
  intro A D Axis t axes equal length shape array sourceAxes haxes hcheck
  simp [Shape.m561, haxes, bind, Except.bind] at hcheck
  exact omittedAxesSingleton equal length shape sourceAxes hcheck

/-- A successful lazy-wrapper instantiation always installs axes, and any source dimensions
omitted by those axes are singleton dimensions. Both source combine_axes and validation
overloads are used, with the real Broadcasted constructor. -/
def InstantiationPreservesVaryingAxes : Prop :=
  ∀ {S F A Axis : Type} {t : IntTy} (axes : A → Shape.Result (List Axis))
      (equal : Axis → Axis → Bool) (length : Axis → JInt t)
      (bc result : Lazy.Broadcasted S F A (Option (List Axis))) (sourceAxes : List Axis),
    axes bc.args = .ok sourceAxes →
    Lazy.m310 (Shape.m504 axes) (Shape.m561 axes equal length) bc = .ok result →
      ∃ outputAxes, result.axes = some outputAxes ∧
        ∀ axis ∈ sourceAxes.drop outputAxes.length, (length axis).val = 1

theorem instantiationPreservesVaryingAxes : InstantiationPreservesVaryingAxes := by
  intro S F A Axis t axes equal length bc result sourceAxes haxes hresult
  cases hb : bc.axes with
  | none =>
    simp [Lazy.m310, Shape.m504, hb, haxes, Lazy.m176, bind, Except.bind, pure, Except.pure] at hresult
    subst result
    exact ⟨sourceAxes, rfl, by simp⟩
  | some outputAxes =>
    cases hc : Shape.m561 axes equal length outputAxes bc.args with
    | error e =>
      simp [Lazy.m310, hb, hc, bind, Except.bind] at hresult
    | ok checked =>
      cases checked
      simp [Lazy.m310, hb, hc, Lazy.m176, bind, Except.bind, pure, Except.pure] at hresult
      subst result
      exact ⟨outputAxes, rfl,
        validationPreservesVaryingAxes axes equal length outputAxes bc.args sourceAxes haxes hc⟩

/-- The tuple-style validation overload obeys the same no-dropped-varying-dimensions rule. -/
def TupleInstantiationPreservesVaryingAxes : Prop :=
  ∀ {S F A Axis : Type} {t : IntTy} (axes : A → Shape.Result (List Axis))
      (equal : Axis → Axis → Bool) (length : Axis → JInt t)
      (bc result : Lazy.Broadcasted S F A (List Axis)) (sourceAxes : List Axis),
    axes bc.args = .ok sourceAxes →
    Lazy.m322 (Shape.m561 axes equal length) bc = .ok result →
      ∀ axis ∈ sourceAxes.drop result.axes.length, (length axis).val = 1

theorem tupleInstantiationPreservesVaryingAxes : TupleInstantiationPreservesVaryingAxes := by
  intro S F A Axis t axes equal length bc result sourceAxes haxes hresult
  cases hc : Shape.m561 axes equal length bc.axes bc.args with
  | error e =>
    simp [Lazy.m322, hc, bind, Except.bind] at hresult
  | ok checked =>
    cases checked
    simp [Lazy.m322, hc, bind, Except.bind, pure, Except.pure] at hresult
    subst result
    exact validationPreservesVaryingAxes axes equal length bc.axes bc.args sourceAxes haxes hc

theorem alignedAxesCompatible {D Axis : Type} {t : IntTy} (equal : D → Axis → Bool)
    (length : Axis → JInt t) (shape : List D) (axes : List Axis)
    (h : Shape.checkShape equal length shape axes = .ok ()) :
    ∀ (i : Nat) (dim : D) (axis : Axis), shape[i]? = some dim → axes[i]? = some axis →
      equal dim axis = true ∨ (length axis).val = 1 := by
  induction shape generalizing axes with
  | nil => simp
  | cons head tail ih =>
    cases axes with
    | nil => simp
    | cons first rest =>
      rw [shapeCons] at h
      cases hc : Shape.m536 equal length head first with
      | false => simp [hc] at h
      | true =>
        simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have hcompat : equal head first = true ∨ (length first).val = 1 := by
          simpa [Shape.m536] using hc
        intro i dim axis hs ha
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hs ha
          subst dim
          subst axis
          exact hcompat
        | succ i =>
          exact ih rest h i dim axis (by simpa using hs) (by simpa using ha)

theorem compatibleShapeAccepted {D Axis : Type} {t : IntTy} (equal : D → Axis → Bool)
    (length : Axis → JInt t) (shape : List D) :
    ∀ axes : List Axis,
      (∀ (i : Nat) dim axis, shape[i]? = some dim → axes[i]? = some axis →
        equal dim axis = true ∨ (length axis).val = 1) →
      (∀ axis ∈ axes.drop shape.length, (length axis).val = 1) →
      Shape.checkShape equal length shape axes = .ok () := by
  induction shape with
  | nil =>
    intro axes _ hdrop
    rw [emptyShape]
    have hall : ∀ axis ∈ axes, (length axis).val = 1 := by simpa using hdrop
    simpa [Shape.m551] using hall
  | cons head tail ih =>
    intro axes halign hdrop
    cases axes with
    | nil => rfl
    | cons first rest =>
      have hhead := halign 0 head first rfl rfl
      have hc : Shape.m536 equal length head first = true := by
        simpa [Shape.m536] using hhead
      rw [shapeCons]
      simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      apply ih rest
      · intro i dim axis hs ha
        exact halign (i + 1) dim axis (by simpa using hs) (by simpa using ha)
      · simpa using hdrop

/-- Shape validation succeeds exactly when every aligned source axis is equal or singleton
and every source axis beyond the destination rank is singleton. -/
def ValidationAlignedAxes : Prop :=
  ∀ {A D Axis : Type} {t : IntTy} (axes : A → Shape.Result (List Axis))
      (equal : D → Axis → Bool) (length : Axis → JInt t)
      (shape : List D) (array : A) (sourceAxes : List Axis),
    axes array = .ok sourceAxes →
    (Shape.m561 axes equal length shape array = .ok () ↔
      (∀ (i : Nat) (dim : D) (axis : Axis), shape[i]? = some dim → sourceAxes[i]? = some axis →
        equal dim axis = true ∨ (length axis).val = 1) ∧
      (∀ axis ∈ sourceAxes.drop shape.length, (length axis).val = 1))

theorem validationAlignedAxes : ValidationAlignedAxes := by
  intro A D Axis t axes equal length shape array sourceAxes haxes
  simp only [Shape.m561, haxes, bind, Except.bind]
  constructor
  · intro hcheck
    exact ⟨alignedAxesCompatible equal length shape sourceAxes hcheck,
      omittedAxesSingleton equal length shape sourceAxes hcheck⟩
  · intro hfit
    exact compatibleShapeAccepted equal length shape sourceAxes hfit.1 hfit.2
theorem unitThenOk {E : Type} (first rest : Except E Unit) :
    (first >>= fun _ => rest) = .ok () ↔ first = .ok () ∧ rest = .ok () := by
  cases first with
  | error error => simp [bind, Except.bind]
  | ok value =>
    cases value
    simp [bind, Except.bind]

/-- Variadic shape validation accepts exactly when every supplied array is broadcast
compatible with the destination. No argument can be skipped during recursion. -/
def EveryArgumentValidated : Prop :=
  ∀ {D A Axis : Type} {t : IntTy} (axes : A → Shape.Result (List Axis))
      (equal : D → Axis → Bool) (length : Axis → JInt t)
      (shape : List D) (first second : A) (rest : List A),
    Shape.m563 axes equal length shape first second rest = .ok () ↔
      ∀ array ∈ first :: second :: rest, Shape.m561 axes equal length shape array = .ok ()

theorem everyArgumentValidated : EveryArgumentValidated := by
  intro D A Axis t axes equal length shape first second rest
  induction rest generalizing first second with
  | nil =>
    rw [Shape.m563.eq_def, unitThenOk]
    simp
  | cons next rest ih =>
    rw [Shape.m563.eq_def, unitThenOk, ih second next]
    simp

end ValidationProofs

namespace ShapeIdentityProofs

/-- Broadcasting a scalar's empty shape against another shape preserves every dimension and
axis of the non-scalar shape, in either argument order. The recursive source overloads are used. -/
def ScalarShapeIdentity : Prop :=
  ∀ {D : Type} (head : D) (tail : List D),
    Shape.m525 head tail = .ok (head :: tail) ∧
    Shape.m526 head tail = .ok (head :: tail)

theorem scalarShapeIdentity : ScalarShapeIdentity := by
  intro D head tail
  induction tail generalizing head with
  | nil =>
    constructor
    · rw [Shape.m525.eq_def]
      rfl
    · rw [Shape.m526.eq_def]
      rfl
  | cons next rest ih =>
    constructor
    · rw [Shape.m525.eq_def]
      simp only [(ih next).1, bind, Except.bind, pure, Except.pure]
    · rw [Shape.m526.eq_def]
      simp only [(ih next).2, bind, Except.bind, pure, Except.pure]
end ShapeIdentityProofs

namespace FlattenProofs

theorem flatNil {S X α : Type} :
    Flatten.isFlatArgs ([] : List (Flatten.Tree S X α)) = true := by
  simp only [Flatten.isFlatArgs.eq_def, Flatten.m367]

theorem flatLeaf {S X α : Type} (value : α) (tail : List (Flatten.Tree S X α)) :
    Flatten.isFlatArgs (.leaf value :: tail) = Flatten.isFlatArgs tail := by
  rw [Flatten.isFlatArgs.eq_def]
  dsimp only
  rw [Flatten.m366.eq_def]

theorem flatNode {S X α : Type} (style : S) (f : List α → Flatten.Result α)
    (args : List (Flatten.Tree S X α)) (axes : X) (tail : List (Flatten.Tree S X α)) :
    Flatten.isFlatArgs (.node style f args axes :: tail) = false := by
  simp only [Flatten.isFlatArgs.eq_def, Flatten.m365]

theorem flatExact {S X α : Type} (args : List (Flatten.Tree S X α)) :
    Flatten.isFlatArgs args = true ↔ ∀ arg ∈ args, ∃ value, arg = .leaf value := by
  induction args with
  | nil => simp [flatNil]
  | cons head tail ih =>
    cases head with
    | leaf value => simpa [flatLeaf] using ih
    | node style f args axes => simp [flatNode]

/-- The flatness predicate is exact: it accepts precisely the argument tuples containing
ordinary leaves and no nested Broadcasted wrapper. -/
def FlatnessExactly : Prop :=
  ∀ {S X α : Type} (bc : Flatten.BroadcastNode S X α),
    Flatten.m364 bc = true ↔ ∀ arg ∈ bc.args, ∃ value, arg = .leaf value

theorem flatnessExactly : FlatnessExactly := by
  intro S X α bc
  exact flatExact bc.args

theorem catNil {S X α : Type} :
    Flatten.catNestedArgs ([] : List (Flatten.Tree S X α)) = [] := by
  simp only [Flatten.catNestedArgs.eq_def, Flatten.m370]

theorem catLeaf {S X α : Type} (value : α) :
    Flatten.catNested (.leaf value : Flatten.Tree S X α) = [.leaf value] := by
  simp only [Flatten.catNested.eq_def, Flatten.m373]

theorem catNode {S X α : Type} (style : S) (f : List α → Flatten.Result α)
    (args : List (Flatten.Tree S X α)) (axes : X) :
    Flatten.catNested (.node style f args axes) = Flatten.catNestedArgs args := by
  rw [Flatten.catNested.eq_def]
  dsimp only
  rw [Flatten.m369.eq_def]

theorem catCons {S X α : Type} (head : Flatten.Tree S X α) (tail : List (Flatten.Tree S X α)) :
    Flatten.catNestedArgs (head :: tail) = Flatten.catNested head ++ Flatten.catNestedArgs tail := by
  cases tail with
  | nil =>
    rw [Flatten.catNestedArgs.eq_def]
    dsimp only
    rw [Flatten.m371.eq_def]
    simp only [catNil, List.append_nil]
  | cons next rest =>
    rw [Flatten.catNestedArgs.eq_def]
    dsimp only
    rw [Flatten.m372.eq_def]

mutual
  inductive Leaves (S X α : Type) : Flatten.Tree S X α → List α → Prop where
    | leaf (value : α) : Leaves S X α (.leaf value) [value]
    | node {style : S} {f : List α → Flatten.Result α} {args : List (Flatten.Tree S X α)}
        {axes : X} {values : List α} :
        ArgumentLeaves S X α args values → Leaves S X α (.node style f args axes) values

  inductive ArgumentLeaves (S X α : Type) : List (Flatten.Tree S X α) → List α → Prop where
    | nil : ArgumentLeaves S X α [] []
    | cons {head : Flatten.Tree S X α} {tail : List (Flatten.Tree S X α)}
        {left right : List α} :
        Leaves S X α head left → ArgumentLeaves S X α tail right →
          ArgumentLeaves S X α (head :: tail) (left ++ right)
end

mutual
  theorem catTreeExactly {S X α : Type} {tree : Flatten.Tree S X α} {values : List α}
      (hleaves : Leaves S X α tree values) :
      Flatten.catNested tree = values.map Flatten.Tree.leaf := by
    cases hleaves with
    | leaf value => simp only [catLeaf, List.map_cons, List.map_nil]
    | @node style f args axes values hargs => simpa only [catNode] using catArgsExactly hargs
  termination_by (Flatten.treeWeight tree, 0)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Flatten.treeWeight]
    all_goals omega

  theorem catArgsExactly {S X α : Type} {args : List (Flatten.Tree S X α)} {values : List α}
      (hleaves : ArgumentLeaves S X α args values) :
      Flatten.catNestedArgs args = values.map Flatten.Tree.leaf := by
    cases hleaves with
    | nil => simp only [catNil, List.map_nil]
    | @cons head tail left right hhead htail =>
      rw [catCons, catTreeExactly hhead, catArgsExactly htail, List.map_append]
  termination_by (Flatten.argsWeight args, 1)
  decreasing_by
    all_goals have hpos := Flatten.treeWeight_pos head
    all_goals simp_wf
    all_goals simp only [Flatten.argsWeight]
    all_goals omega
end

mutual
  theorem leavesTotal {S X α : Type} (tree : Flatten.Tree S X α) :
      ∃ values, Leaves S X α tree values := by
    cases tree with
    | leaf value => exact ⟨[value], .leaf value⟩
    | node style f args axes =>
      obtain ⟨values, hv⟩ := argumentLeavesTotal args
      exact ⟨values, .node hv⟩
  termination_by (Flatten.treeWeight tree, 0)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Flatten.treeWeight]
    all_goals omega

  theorem argumentLeavesTotal {S X α : Type} (args : List (Flatten.Tree S X α)) :
      ∃ values, ArgumentLeaves S X α args values := by
    cases args with
    | nil => exact ⟨[], .nil⟩
    | cons head tail =>
      obtain ⟨left, hl⟩ := leavesTotal head
      obtain ⟨right, hr⟩ := argumentLeavesTotal tail
      exact ⟨left ++ right, .cons hl hr⟩
  termination_by (Flatten.argsWeight args, 1)
  decreasing_by
    all_goals have hpos := Flatten.treeWeight_pos head
    all_goals simp_wf
    all_goals simp only [Flatten.argsWeight]
    all_goals omega
end

/-- Concatenating nested broadcast arguments retains every original leaf in depth-first
argument order. The semantic relation describes the tree's leaves independently of the code. -/
def ConcatenatedLeafOrder : Prop :=
  ∀ {S X α : Type} (bc : Flatten.BroadcastNode S X α) (values : List α),
    ArgumentLeaves S X α bc.args values →
      Flatten.m369 bc = values.map Flatten.Tree.leaf

theorem concatenatedLeafOrder : ConcatenatedLeafOrder := by
  intro S X α bc values hv
  rw [Flatten.m369.eq_def]
  exact catArgsExactly hv

theorem catFlatIdentity {S X α : Type} (args : List (Flatten.Tree S X α)) :
    Flatten.isFlatArgs args = true → Flatten.catNestedArgs args = args := by
  induction args with
  | nil => intro _; exact catNil
  | cons head tail ih =>
    intro hflat
    cases head with
    | leaf value =>
      have ht : Flatten.isFlatArgs tail = true := by simpa only [flatLeaf] using hflat
      rw [catCons, catLeaf, ih ht]
      rfl
    | node style f args axes => simp only [flatNode, Bool.false_eq_true] at hflat

theorem flattenSequence {S X α : Type} (bc : Flatten.BroadcastNode S X α) (values : List α)
    (hv : ArgumentLeaves S X α bc.args values) :
    (Flatten.m346 JuliaLean.base.tuple.getindexInt
      JuliaLean.base.operators.maybeConstructorValue bc).args = values.map Flatten.Tree.leaf := by
  by_cases hf : Flatten.m364 bc = true
  · simp only [Flatten.m346, hf, ↓reduceIte]
    have hflat : Flatten.isFlatArgs bc.args = true := hf
    exact (catFlatIdentity bc.args hflat).symm.trans (catArgsExactly hv)
  · simp only [Flatten.m346, hf]
    rw [Flatten.m369.eq_def]
    exact catArgsExactly hv

/-- Flattening removes every nested argument wrapper, retains the complete ordered sequence
of leaves, and preserves the outer style and output axes. All Julia callees are concrete. -/
def FlattenPreservesLeaves : Prop :=
  ∀ {S X α : Type} (bc : Flatten.BroadcastNode S X α),
    let flat := Flatten.m346 JuliaLean.base.tuple.getindexInt
      JuliaLean.base.operators.maybeConstructorValue bc
    (∀ arg ∈ flat.args, ∃ value, arg = .leaf value) ∧
    (∀ values, ArgumentLeaves S X α bc.args values → flat.args = values.map Flatten.Tree.leaf) ∧
    flat.style = bc.style ∧ flat.axes = bc.axes

theorem flattenPreservesLeaves : FlattenPreservesLeaves := by
  intro S X α bc
  obtain ⟨values, hv⟩ := argumentLeavesTotal bc.args
  have hseq := flattenSequence bc values hv
  refine ⟨?_, fun values hv => flattenSequence bc values hv, ?_⟩
  · rw [hseq]
    intro arg hm
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp hm
    exact ⟨value, rfl⟩
  · by_cases hf : Flatten.m364 bc = true <;> simp [Flatten.m346, hf]

/-- A leaf selector reads exactly its one-based tuple position, and invalid positions report
BoundsError. The selector uses the real Pick call and the real tuple indexing method. -/
def LeafPickerCorrect : Prop :=
  ∀ {α : Type} (args : List α) (leaf : α) (n : Flatten.Cursor),
    (∀ (i : Nat) (hi : i < args.length), n.val = (i : Int) + 1 →
      (Flatten.m398 JuliaLean.base.tuple.getindexInt leaf n).1 args = .ok args[i]) ∧
    (¬ (1 ≤ n.val ∧ n.val ≤ args.length) →
      (Flatten.m398 JuliaLean.base.tuple.getindexInt leaf n).1 args = .error (.julia .boundsError))

theorem leafPickerCorrect : LeafPickerCorrect := by
  intro α args leaf n
  constructor
  · intro i hi hn
    change JuliaLean.base.tuple.getfield args n.val = .ok args[i]
    rw [hn]
    unfold JuliaLean.base.tuple.getfield
    have hpos : (1 : Int) ≤ (i : Int) + 1 := by omega
    have hindex : ((i : Int) + 1 - 1).toNat = i := by omega
    rw [ite_eq_left hpos, hindex, List.getElem?_eq_getElem hi]
  · intro hbad
    change JuliaLean.base.tuple.getfield args n.val = .error (.julia .boundsError)
    unfold JuliaLean.base.tuple.getfield
    by_cases hpos : 1 ≤ n.val
    · have hindex : args.length ≤ (n.val - 1).toNat := by omega
      simp only [hpos, ↓reduceIte, List.getElem?_eq_none hindex, JuliaLean.base.tuple.bounds]
    · simp only [hpos, ↓reduceIte, JuliaLean.base.tuple.bounds]

theorem makeManyLength {S X α : Type} (args : List (Flatten.Tree S X α)) (n : Flatten.Cursor) :
    (Flatten.makeMany JuliaLean.base.tuple.getindexInt
      JuliaLean.base.operators.maybeConstructorValue args n).1.length = args.length := by
  induction args generalizing n with
  | nil =>
    rw [Flatten.makeMany.eq_def]
    rfl
  | cons head tail ih =>
    rw [Flatten.makeMany.eq_def]
    dsimp only
    rw [Flatten.m386.eq_def]
    dsimp only
    simp only [List.length_cons, ih]

/-- The selector builder produces one evaluator per original argument, including arguments
that are themselves nested broadcast expressions. -/
def SelectorArity : Prop :=
  ∀ {S X α : Type} (args : List (Flatten.Tree S X α)),
    (Flatten.m382 JuliaLean.base.tuple.getindexInt
      JuliaLean.base.operators.maybeConstructorValue args).length = args.length

theorem selectorArity : SelectorArity := by
  intro S X α args
  exact makeManyLength args (JInt.lit .i64 1)

theorem prepareCons {α : Type} (head : Flatten.Selector α) (tail : List (Flatten.Selector α))
    (input : List α) :
    Flatten.prepareArgs (head :: tail) input = (do
      let first ← head input
      let rest ← Flatten.prepareArgs tail input
      pure (first :: rest)) := by
  cases tail with
  | nil =>
    rw [Flatten.prepareArgs.eq_def]
    dsimp only
    cases hh : head input <;>
      simp [Flatten.m408, Flatten.prepareArgs.eq_def, Flatten.m409, hh, bind, Except.bind, pure, Except.pure]
  | cons next rest =>
    rw [Flatten.prepareArgs.eq_def]
    dsimp only
    rw [Flatten.m407.eq_def]

theorem prepareLength {α : Type} (selectors : List (Flatten.Selector α)) (input output : List α)
    (h : Flatten.prepareArgs selectors input = .ok output) :
    output.length = selectors.length := by
  induction selectors generalizing output with
  | nil =>
    simp [Flatten.prepareArgs.eq_def, Flatten.m409] at h
    subst output
    rfl
  | cons head tail ih =>
    rw [prepareCons] at h
    cases hh : head input with
    | error e => simp [hh, bind, Except.bind] at h
    | ok value =>
      cases ht : Flatten.prepareArgs tail input with
      | error e => simp [hh, ht, bind, Except.bind] at h
      | ok rest =>
        simp [hh, ht, bind, Except.bind, pure, Except.pure] at h
        subst output
        have hrest := ih rest ht
        simp [hrest]

/-- Preparing the actual generated selector tuple retains one result for every original
broadcast argument. No input is omitted or duplicated by the recursive tuple preparation. -/
def PreparedArgumentArity : Prop :=
  ∀ {S X α : Type} (args : List (Flatten.Tree S X α)) (input output : List α),
    Flatten.prepareArgs (Flatten.m382 JuliaLean.base.tuple.getindexInt
      JuliaLean.base.operators.maybeConstructorValue args) input = .ok output →
      output.length = args.length

theorem preparedArgumentArity : PreparedArgumentArity := by
  intro S X α args input output h
  exact (prepareLength _ input output h).trans (selectorArity args)

/-- A one-leaf nested evaluator calls its original function on the selected leaf value.
Errors returned by that function are preserved as well as successful values. -/
def NestedSingleLeafEvaluation : Prop :=
  ∀ {S X α : Type} (f : List α → Flatten.Result α) (leaf : α)
      (n : Flatten.Cursor) (input : List α) (i : Nat) (hi : i < input.length),
    n.val = (i : Int) + 1 →
      (Flatten.m400 JuliaLean.base.tuple.getindexInt
        JuliaLean.base.operators.maybeConstructorValue f
        ([.leaf leaf] : List (Flatten.Tree S X α)) n).1 input = f [input[i]]

theorem nestedSingleLeafEvaluation : NestedSingleLeafEvaluation := by
  intro S X α f leaf n input i hi hn
  have hpick : Flatten.m395 JuliaLean.base.tuple.getindexInt n input = .ok input[i] :=
    (leafPickerCorrect input leaf n).1 i hi hn
  rw [Flatten.m400.eq_def]
  simp only [Flatten.makeMany.eq_def, Flatten.m386.eq_def, Flatten.makeOne.eq_def,
    Flatten.m398, Flatten.m391, JuliaLean.base.operators.maybeConstructorValue,
    Flatten.prepareArgs.eq_def, Flatten.m408, hpick, bind, Except.bind, pure, Except.pure]
end FlattenProofs

namespace BooleanProofs

theorem broadcastableMap {A : Type} (args : List A) :
    args.mapM (Material.m738 (μ := Except Style.StyleError)) = .ok args := by
  induction args with
  | nil => rfl
  | cons head tail ih =>
    simp [List.mapM_cons, Material.m738, ih, bind, Except.bind, pure, Except.pure]

theorem nonemptySyntaxFields {A F X : Type}
    (ndims : A → Except Style.StyleError Style.Rank) (f : F) (first : A) (rest : List A)
    (result : Syntax.Broadcasted Style.Style F A X)
    (h : Syntax.m1409 Material.m738
      (Style.combineStyles (Style.m432 (Style.m103 ndims)) (Style.m459 (· = ·)))
      Syntax.m1420 f first rest = .ok result) :
    result.f = f ∧ result.args = first :: rest ∧ result.axes = none := by
  cases hs : Style.combineStyles (Style.m432 (Style.m103 ndims)) (Style.m459 (· = ·)) (first :: rest) with
  | error e =>
    simp [Syntax.m1409, Material.m738, broadcastableMap, hs, bind, Except.bind,
      pure, Except.pure] at h
  | ok style =>
    simp [Syntax.m1409, Material.m738, broadcastableMap, hs, Syntax.m1420, Lazy.m176,
      bind, Except.bind, pure, Except.pure] at h
    subst result
    exact ⟨rfl, rfl, rfl⟩

/-- Boolean broadcasting suppresses the nested evaluation exactly on the short-circuit
branch. On the other branch it preserves the flattened evaluator's values and errors.
Flatten, broadcastable, style discovery, result_style, broadcasted and constructors are real. -/
def ShortCircuitNested : Prop :=
  ∀ {S X : Type} (ndims : Flatten.Tree S X Bool → Except Style.StyleError Style.Rank)
      (first : Flatten.Tree S X Bool) (bc : Flatten.BroadcastNode S X Bool)
      (result : Syntax.Broadcasted Style.Style (Bool → List Bool → Flatten.Result Bool)
        (Flatten.Tree S X Bool) Unit),
    (Lazy.m199 (Flatten.m346 JuliaLean.base.tuple.getindexInt
      JuliaLean.base.operators.maybeConstructorValue)
      (Syntax.m1409 Material.m738
        (Style.combineStyles (Style.m432 (Style.m103 ndims)) (Style.m459 (· = ·)))
        Syntax.m1420) first bc = .ok result →
      (∀ values, result.f false values = .ok false ∧
        result.f true values = (Flatten.m346 JuliaLean.base.tuple.getindexInt
          JuliaLean.base.operators.maybeConstructorValue bc).f values) ∧
      result.args = first :: (Flatten.m346 JuliaLean.base.tuple.getindexInt
        JuliaLean.base.operators.maybeConstructorValue bc).args) ∧
    (Lazy.m208 (Flatten.m346 JuliaLean.base.tuple.getindexInt
      JuliaLean.base.operators.maybeConstructorValue)
      (Syntax.m1409 Material.m738
        (Style.combineStyles (Style.m432 (Style.m103 ndims)) (Style.m459 (· = ·)))
        Syntax.m1420) first bc = .ok result →
      (∀ values, result.f true values = .ok true ∧
        result.f false values = (Flatten.m346 JuliaLean.base.tuple.getindexInt
          JuliaLean.base.operators.maybeConstructorValue bc).f values) ∧
      result.args = first :: (Flatten.m346 JuliaLean.base.tuple.getindexInt
        JuliaLean.base.operators.maybeConstructorValue bc).args)

theorem shortCircuitNested : ShortCircuitNested := by
  intro S X ndims first bc result
  constructor
  · intro h
    obtain ⟨hf, ha, _⟩ := nonemptySyntaxFields ndims _ first _ result h
    exact ⟨fun values => by rw [hf]; exact ⟨rfl, rfl⟩, ha⟩
  · intro h
    obtain ⟨hf, ha, _⟩ := nonemptySyntaxFields ndims _ first _ result h
    exact ⟨fun values => by rw [hf]; exact ⟨rfl, rfl⟩, ha⟩
end BooleanProofs

namespace TypedShapeProofs

/-- Integer singleton expansion accepts exactly equal or singleton dimensions, across every
pair of bit-integer widths, and retains an input value with its original integer type. -/
def IntegerDimensionJoin : Prop :=
  ∀ (a b : Shape.IntegerDimension),
    (∀ result, Shape.integerJoin a b = .ok result →
      (a.2.val = 1 ∨ a.2.val = result.2.val) ∧
      (b.2.val = 1 ∨ b.2.val = result.2.val) ∧ (result = a ∨ result = b)) ∧
    (Shape.integerJoin a b = .error .dimensionMismatch ↔
      a.2.val ≠ 1 ∧ b.2.val ≠ 1 ∧ a.2.val ≠ b.2.val)

theorem integerDimensionJoin : IntegerDimensionJoin := by
  intro a b
  by_cases ha : a.2.val = 1
  · simp [Shape.integerJoin, Shape.m531, ha, bind, Except.bind, pure, Except.pure]
  · by_cases hb : b.2.val = 1
    · simp [Shape.integerJoin, Shape.m531, ha, hb, bind, Except.bind, pure, Except.pure]
    · by_cases he : a.2.val = b.2.val
      · simp [Shape.integerJoin, Shape.m531, ha, hb, he, bind, Except.bind, pure, Except.pure]
      · simp [Shape.integerJoin, Shape.m531, ha, hb, he, bind, Except.bind, pure, Except.pure]

theorem nonemptyShapeRank {D : Type} (join : D → D → Shape.Result D)
    (headA : D) (tailA : List D) (headB : D) (tailB : List D) (out : List D)
    (h : Shape.m527 join headA tailA headB tailB = .ok out) :
    out.length = max (headA :: tailA).length (headB :: tailB).length := by
  rw [Shape.m527.eq_def] at h
  cases hj : join headA headB with
  | error error => simp [hj, bind, Except.bind] at h
  | ok head =>
    rw [hj] at h
    cases tailA with
    | nil =>
      cases tailB with
      | nil =>
        simp [Shape.m524, bind, Except.bind, pure, Except.pure] at h
        subst out
        rfl
      | cons next rest =>
        dsimp only [bind, Except.bind] at h
        rw [(ShapeIdentityProofs.scalarShapeIdentity next rest).1] at h
        simp [bind, Except.bind, pure, Except.pure] at h
        subst out
        simp
    | cons nextA restA =>
      cases tailB with
      | nil =>
        dsimp only [bind, Except.bind] at h
        rw [(ShapeIdentityProofs.scalarShapeIdentity nextA restA).2] at h
        simp [bind, Except.bind, pure, Except.pure] at h
        subst out
        simp
      | cons nextB restB =>
        cases ht : Shape.m527 join nextA restA nextB restB with
        | error error =>
          simp [ht, bind, Except.bind] at h
        | ok tail =>
          simp [ht, bind, Except.bind, pure, Except.pure] at h
          subst out
          have ih := nonemptyShapeRank join nextA restA nextB restB tail ht
          simp only [List.length_cons] at ih ⊢
          omega
termination_by tailA.length + tailB.length

theorem binaryShapeRank {D : Type} (join : D → D → Shape.Result D)
    (a b out : List D) (h : Shape.bcsDispatch join a b = .ok out) :
    out.length = max a.length b.length := by
  cases a with
  | nil =>
    cases b with
    | nil =>
      simp [Shape.bcsDispatch, Shape.m524, pure, Except.pure] at h
      subst out
      rfl
    | cons head tail =>
      simp only [Shape.bcsDispatch] at h
      rw [(ShapeIdentityProofs.scalarShapeIdentity head tail).1] at h
      cases h
      simp
  | cons headA tailA =>
    cases b with
    | nil =>
      simp only [Shape.bcsDispatch] at h
      rw [(ShapeIdentityProofs.scalarShapeIdentity headA tailA).2] at h
      cases h
      simp
    | cons headB tailB => exact nonemptyShapeRank join headA tailA headB tailB out h

theorem variadicShapeRank {D : Type} (join : D → D → Shape.Result D)
    (shape next : List D) (rest : List (List D)) (out : List D)
    (h : Shape.m522 (Shape.bcsDispatch join) shape next rest = .ok out) :
    out.length = (shape :: next :: rest).foldr (fun dims n => max dims.length n) 0 := by
  rw [Shape.m522.eq_def] at h
  cases hc : Shape.bcsDispatch join shape next with
  | error e => simp [hc, bind, Except.bind] at h
  | ok combined =>
    have hrank := binaryShapeRank join shape next combined hc
    rw [hc] at h
    cases rest with
    | nil =>
      simp [Shape.m521, bind, Except.bind, pure, Except.pure] at h
      subst out
      simpa using hrank
    | cons after remaining =>
      simp only [bind, Except.bind] at h
      have ih := variadicShapeRank join combined after remaining out h
      simpa only [List.foldr_cons, hrank, Nat.max_assoc] using ih
termination_by rest.length

/-- Successful integer broadcast shape combination keeps the largest argument rank.
The inputs may mix all ten bit-integer types; the recursive numbered overloads and
the numbered integer singleton-expansion method are used throughout. -/
def IntegerShapeRank : Prop :=
  ∀ (shape : List Shape.IntegerDimension) (rest : List (List Shape.IntegerDimension))
      (out : List Shape.IntegerDimension),
    Shape.shapeDispatch Shape.integerJoin shape rest = .ok out →
      out.length = (shape :: rest).foldr (fun dims n => max dims.length n) 0

theorem integerShapeRank : IntegerShapeRank := by
  intro shape rest out h
  cases rest with
  | nil =>
    simp [Shape.shapeDispatch, Shape.m521, pure, Except.pure] at h
    subst out
    simp
  | cons next rest => exact variadicShapeRank Shape.integerJoin shape next rest out h

/-- Mixing an integer dimension with an axis retains that axis exactly when the integer is
one or the axis starts at one and ends at the integer dimension. Both argument orders and
all participating bit-integer widths are included. -/
def IntegerAxisCompatibility : Prop :=
  ∀ {t u v : IntTy} {A : Type} (first : A → JInt u) (last : A → JInt v)
      (n : JInt t) (axis : A),
    let compatible := n.val = 1 ∨ ((first axis).val = 1 ∧ (last axis).val = n.val)
    (∀ result, Shape.m532 first last n axis = .ok result ↔ result = axis ∧ compatible) ∧
    (∀ result, Shape.m533 first last axis n = .ok result ↔ result = axis ∧ compatible) ∧
    (Shape.m532 first last n axis = .error .dimensionMismatch ↔ ¬ compatible) ∧
    (Shape.m533 first last axis n = .error .dimensionMismatch ↔ ¬ compatible)

theorem integerAxisCompatibility : IntegerAxisCompatibility := by
  intro t u v A first last n axis
  by_cases hn : n.val = 1
  · simp [Shape.m532, Shape.m533, hn, eq_comm]
  · by_cases ha : (first axis).val = 1 ∧ (last axis).val = n.val
    · simp [Shape.m532, Shape.m533, hn, ha, eq_comm]
    · simp [Shape.m532, Shape.m533, hn, ha]

/-- Axis combination rejects exactly unequal non-singleton axes. Successful combination
retains a complete input axis and the length required by each non-singleton input. -/
def AxisCombination : Prop :=
  ∀ {A : Type} {t : IntTy} (equal : A → A → Bool) (length : A → JInt t),
    (∀ a b, equal a b = true ↔ a = b) →
    ∀ a b : A,
      (Shape.m534 Shape.Error.dimensionMismatch (Shape.m536 equal length) (Shape.m536 equal length)
        Shape.m542 Shape.m542 a b = .error .dimensionMismatch ↔
          a ≠ b ∧ (length a).val ≠ 1 ∧ (length b).val ≠ 1) ∧
      (∀ result, Shape.m534 Shape.Error.dimensionMismatch (Shape.m536 equal length) (Shape.m536 equal length)
        Shape.m542 Shape.m542 a b = .ok result →
          (result = a ∨ result = b) ∧
          ((length a).val = 1 ∨ (length result).val = (length a).val) ∧
          ((length b).val = 1 ∨ (length result).val = (length b).val))

theorem axisCombination : AxisCombination := by
  intro A t equal length hequal a b
  by_cases heq : a = b
  · subst b
    simp [Shape.m534, Shape.m536, Shape.m542, hequal, pure, Except.pure]
  · by_cases ha : (length a).val = 1
    · simp [Shape.m534, Shape.m536, Shape.m542, hequal, heq, Ne.symm heq, ha,
        pure, Except.pure]
    · by_cases hb : (length b).val = 1
      · simp [Shape.m534, Shape.m536, Shape.m542, hequal, heq, Ne.symm heq, ha, hb,
          pure, Except.pure]
      · simp [Shape.m534, Shape.m536, Shape.m542, hequal, heq, Ne.symm heq, ha, hb]

/-- Combining axis-valued shapes retains exactly the largest input rank. The extent
compatibility predicates and same-type axis constructor are the real source methods. -/
def AxisShapeRank : Prop :=
  ∀ {A : Type} {t : IntTy} (equal : A → A → Bool) (length : A → JInt t)
      (shape : List A) (rest : List (List A)) (out : List A),
    Shape.shapeDispatch
      (Shape.m534 Shape.Error.dimensionMismatch (Shape.m536 equal length) (Shape.m536 equal length)
        Shape.m542 Shape.m542) shape rest = .ok out →
      out.length = (shape :: rest).foldr (fun dims n => max dims.length n) 0

theorem axisShapeRank : AxisShapeRank := by
  intro A t equal length shape rest out h
  cases rest with
  | nil =>
    simp [Shape.shapeDispatch, Shape.m521, pure, Except.pure] at h
    subst out
    simp
  | cons next rest =>
    exact variadicShapeRank
      (Shape.m534 Shape.Error.dimensionMismatch (Shape.m536 equal length) (Shape.m536 equal length)
        Shape.m542 Shape.m542) shape next rest out h

/-- Numeric compatibility allows an equal extent or a singleton right extent. A numeric
right extent compared against a nonnumeric axis must itself be singleton. -/
def NumericCompatibility : Prop :=
  ∀ {A : Type} {t u : IntTy} (equal : JInt t → JInt u → Bool)
      (equalOne : JInt u → Bool),
    (∀ a b, equal a b = true ↔ a.val = b.val) →
    (∀ b, equalOne b = true ↔ b.val = 1) →
    (∀ (axis : A) (b : JInt u), Shape.m537 equalOne axis b = true ↔ b.val = 1) ∧
    (∀ (a : JInt t) (b : JInt u), Shape.m538 equal equalOne a b = true ↔
      a.val = b.val ∨ b.val = 1)

theorem numericCompatibility : NumericCompatibility := by
  intro A t u equal equalOne hequal hone
  simp [Shape.m537, Shape.m538, Bool.or_eq_true, hequal, hone]

end TypedShapeProofs
namespace SizesProofs
open JuliaLean.base.broadcast.Sizes

open JuliaLean

theorem bcs1_eq (a b : I64) :
    bcs1 a b = if a.val = 1 then .ok b else if b.val = 1 then .ok a
      else if a.val = b.val then .ok a else .error .dimensionMismatch := by
  by_cases ha : a.val = 1
  · simp [bcs1, Shape.m531, ha, Except.map]
  · by_cases hb : b.val = 1
    · simp [bcs1, Shape.m531, ha, hb, Except.map]
    · by_cases he : a.val = b.val <;> simp [bcs1, Shape.m531, ha, hb, he, Except.map]

theorem bcs_eq_nil_nil :
    Shape.bcsDispatch bcs1 [] [] = .ok [] := rfl

theorem bcs_eq_nil_cons (b : I64) (bs : List I64) :
    Shape.bcsDispatch bcs1 [] (b :: bs) =
      (do let rest ← Shape.bcsDispatch bcs1 [] bs; pure (b :: rest)) := by
  cases bs with
  | nil =>
    simp only [Shape.bcsDispatch]
    rw [Shape.m525.eq_def]
  | cons next rest =>
    simp only [Shape.bcsDispatch]
    rw [Shape.m525.eq_def]

theorem bcs_eq_cons_nil (a : I64) (as : List I64) :
    Shape.bcsDispatch bcs1 (a :: as) [] =
      (do let rest ← Shape.bcsDispatch bcs1 as []; pure (a :: rest)) := by
  cases as with
  | nil =>
    simp only [Shape.bcsDispatch]
    rw [Shape.m526.eq_def]
  | cons next rest =>
    simp only [Shape.bcsDispatch]
    rw [Shape.m526.eq_def]

theorem bcs_eq_cons_cons (a : I64) (as : List I64) (b : I64) (bs : List I64) :
    Shape.bcsDispatch bcs1 (a :: as) (b :: bs) =
      (do let head ← bcs1 a b; let rest ← Shape.bcsDispatch bcs1 as bs; pure (head :: rest)) := by
  simp only [Shape.bcsDispatch]
  rw [Shape.m527.eq_def]
  cases as <;> cases bs <;> rfl

theorem broadcastShape_eq_nil (shape : List I64) :
    Shape.shapeDispatch bcs1 shape [] = .ok shape := rfl

theorem broadcastShape_eq_cons (shape next : List I64) (rest : List (List I64)) :
    Shape.shapeDispatch bcs1 shape (next :: rest) =
      (do let combined ← Shape.bcsDispatch bcs1 shape next
          Shape.shapeDispatch bcs1 combined rest) := by
  simp only [Shape.shapeDispatch]
  rw [Shape.m522.eq_def]
  cases rest <;> rfl

/-- `Broadcast.broadcast_shape(s, ss...)` on integer size tuples returns the documented
combination: as many dimensions as the longest tuple, and in each dimension every input extent
is 1 or equal to the result extent, which is one of the input extents. It throws only
`DimensionMismatch`, and only when two input extents of one dimension differ and neither is 1. -/
def ShapeCombination : Prop :=
  ∀ (s : List I64) (ss : List (List I64)),
    (∀ out, (Shape.shapeDispatch bcs1) s ss = .ok out →
      out.length = maxLen (s :: ss) ∧
      (∀ d, ∀ t ∈ s :: ss, ext t d = 1 ∨ ext t d = ext out d) ∧
      (∀ d, ∃ t ∈ s :: ss, ext t d = ext out d)) ∧
    (∀ e, (Shape.shapeDispatch bcs1) s ss = .error e →
      e = .dimensionMismatch ∧
      ∃ d, ∃ t ∈ s :: ss, ∃ t' ∈ s :: ss, ext t d ≠ 1 ∧ ext t' d ≠ 1 ∧ ext t d ≠ ext t' d)

/-- `_bcs1` on a size and an axis (in either order) agrees with integer sizes: it throws exactly
when both lengths differ from 1 and from each other, and otherwise returns an entry whose length
is the non-singleton one. -/
def ShapeMixedSingleton : Prop :=
  ∀ x y : Dim,
    (bcs1Mixed x y = .error .dimensionMismatch ↔ (x.len ≠ 1 ∧ y.len ≠ 1 ∧ x.len ≠ y.len)) ∧
    ∀ z, bcs1Mixed x y = .ok z → z.len = (if x.len = 1 then y.len else x.len)

private theorem ext_nil (d : Nat) : ext [] d = 1 := by simp [ext]
private theorem ext_cons_zero (x : I64) (s : List I64) : ext (x :: s) 0 = x.val := by simp [ext]
private theorem ext_cons_succ (x : I64) (s : List I64) (d : Nat) : ext (x :: s) (d + 1) = ext s d := by
  simp [ext]

private theorem bcs1_ok {a b x : I64} (h : bcs1 a b = .ok x) :
    (a.val = 1 ∨ a.val = x.val) ∧ (b.val = 1 ∨ b.val = x.val) ∧ (x.val = a.val ∨ x.val = b.val) := by
  rw [bcs1_eq] at h
  by_cases h1 : a.val = 1
  · simp [h1] at h; subst h; simp [h1]
  · by_cases h2 : b.val = 1
    · simp [h1, h2] at h; subst h; simp [h2]
    · by_cases h3 : a.val = b.val
      · simp [h2, h3] at h; subst h; simp [h3]
      · simp [h1, h2, h3] at h

private theorem bcs1_err {a b : I64} {e : Err} (h : bcs1 a b = .error e) :
    e = .dimensionMismatch ∧ a.val ≠ 1 ∧ b.val ≠ 1 ∧ a.val ≠ b.val := by
  rw [bcs1_eq] at h
  by_cases h1 : a.val = 1
  · simp [h1] at h
  · by_cases h2 : b.val = 1
    · simp [h1, h2] at h
    · by_cases h3 : a.val = b.val
      · simp [h2, h3] at h
      · simp [h1, h2, h3] at h; exact ⟨h.symm, h1, h2, h3⟩

/-- Per-dimension facts about a successful `_bcs`. -/
private def BcsOk (a b u : List I64) : Prop :=
  u.length = max a.length b.length ∧
    ∀ d, (ext a d = 1 ∨ ext a d = ext u d) ∧ (ext b d = 1 ∨ ext b d = ext u d) ∧
      (ext u d = ext a d ∨ ext u d = ext b d)

private theorem bcs_ok : ∀ (a b u : List I64), (Shape.bcsDispatch bcs1) a b = .ok u → BcsOk a b u
  | [], [], u, h => by
    simp [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h; subst h
    exact ⟨rfl, fun d => by simp [ext_nil]⟩
  | [], b :: bs, u, h => by
    simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h
    cases hr : (Shape.bcsDispatch bcs1) [] bs with
    | error e => rw [hr] at h; cases h
    | ok r =>
      rw [hr] at h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hl, hd⟩ := bcs_ok [] bs r hr
      refine ⟨by simp at hl ⊢; omega, fun d => ?_⟩
      cases d with
      | zero => simp [ext_nil, ext_cons_zero]
      | succ d =>
        have := hd d
        simp only [ext_nil, ext_cons_succ] at this ⊢
        exact this
  | a :: as, [], u, h => by
    simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h
    cases hr : (Shape.bcsDispatch bcs1) as [] with
    | error e => rw [hr] at h; cases h
    | ok r =>
      rw [hr] at h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hl, hd⟩ := bcs_ok as [] r hr
      refine ⟨by simp at hl ⊢; omega, fun d => ?_⟩
      cases d with
      | zero => simp [ext_nil, ext_cons_zero]
      | succ d =>
        have := hd d
        simp only [ext_nil, ext_cons_succ] at this ⊢
        exact this
  | a :: as, b :: bs, u, h => by
    simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h
    cases hx : bcs1 a b with
    | error e => rw [hx] at h; cases h
    | ok x =>
      rw [hx] at h
      cases hr : (Shape.bcsDispatch bcs1) as bs with
      | error e => simp only [bind, Except.bind, hr] at h; cases h
      | ok r =>
        simp only [bind, Except.bind, hr, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hd⟩ := bcs_ok as bs r hr
        refine ⟨by simp at hl ⊢; omega, fun d => ?_⟩
        cases d with
        | zero =>
          simp only [ext_cons_zero]
          exact bcs1_ok hx
        | succ d =>
          simp only [ext_cons_succ]
          exact hd d

private theorem bcs_err : ∀ (a b : List I64) (e : Err), (Shape.bcsDispatch bcs1) a b = .error e →
    e = .dimensionMismatch ∧ ∃ d, ext a d ≠ 1 ∧ ext b d ≠ 1 ∧ ext a d ≠ ext b d
  | [], [], e, h => by simp [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h
  | [], b :: bs, e, h => by
    simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h
    cases hr : (Shape.bcsDispatch bcs1) [] bs with
    | error e' =>
      rw [hr] at h
      simp only [bind, Except.bind, Except.error.injEq] at h
      subst h
      obtain ⟨_, d, h1, _, _⟩ := bcs_err [] bs e' hr
      exact absurd (ext_nil d) h1
    | ok r => rw [hr] at h; cases h
  | a :: as, [], e, h => by
    simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h
    cases hr : (Shape.bcsDispatch bcs1) as [] with
    | error e' =>
      rw [hr] at h
      simp only [bind, Except.bind, Except.error.injEq] at h
      subst h
      obtain ⟨_, d, _, h2, _⟩ := bcs_err as [] e' hr
      exact absurd (ext_nil d) h2
    | ok r => rw [hr] at h; cases h
  | a :: as, b :: bs, e, h => by
    simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons] at h
    cases hx : bcs1 a b with
    | error e' =>
      rw [hx] at h
      simp only [bind, Except.bind, Except.error.injEq] at h
      subst h
      obtain ⟨he, h1, h2, h3⟩ := bcs1_err hx
      exact ⟨he, 0, by simpa [ext_cons_zero] using h1, by simpa [ext_cons_zero] using h2,
        by simpa [ext_cons_zero] using h3⟩
    | ok x =>
      rw [hx] at h
      cases hr : (Shape.bcsDispatch bcs1) as bs with
      | error e' =>
        simp only [bind, Except.bind, hr, Except.error.injEq] at h
        subst h
        obtain ⟨he, d, h1, h2, h3⟩ := bcs_err as bs e' hr
        exact ⟨he, d + 1, by simpa [ext_cons_succ] using h1, by simpa [ext_cons_succ] using h2,
          by simpa [ext_cons_succ] using h3⟩
      | ok r => simp only [bind, Except.bind, hr, pure, Except.pure] at h; cases h

private theorem maxLen_cons (s : List I64) (ss : List (List I64)) :
    maxLen (s :: ss) = max s.length (maxLen ss) := rfl

theorem shapeCombination : ShapeCombination := by
  intro s ss
  induction ss generalizing s with
  | nil =>
    refine ⟨fun out h => ?_, fun e h => ?_⟩
    · simp [broadcastShape_eq_nil, broadcastShape_eq_cons] at h; subst h
      refine ⟨by simp [maxLen], fun d t ht => ?_, fun d => ⟨s, by simp, rfl⟩⟩
      simp at ht; subst ht; exact Or.inr rfl
    · simp [broadcastShape_eq_nil, broadcastShape_eq_cons] at h
  | cons t ts ih =>
    refine ⟨fun out h => ?_, fun e h => ?_⟩
    · simp only [broadcastShape_eq_nil, broadcastShape_eq_cons] at h
      cases hu : (Shape.bcsDispatch bcs1) s t with
      | error e => rw [hu] at h; cases h
      | ok u =>
        simp only [bind, Except.bind, hu] at h
        obtain ⟨hl, hd⟩ := bcs_ok s t u hu
        obtain ⟨hl', hall, hex⟩ := (ih u).1 out h
        refine ⟨?_, fun d x hx => ?_, fun d => ?_⟩
        · rw [hl', maxLen_cons, maxLen_cons, maxLen_cons, hl]; omega
        · have hud := hall d u (by simp)
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · rcases (hd d).1 with h1 | h1
            · exact Or.inl h1
            · rcases hud with h2 | h2
              · exact Or.inl (h1.trans h2)
              · exact Or.inr (h1.trans h2)
          · rcases (hd d).2.1 with h1 | h1
            · exact Or.inl h1
            · rcases hud with h2 | h2
              · exact Or.inl (h1.trans h2)
              · exact Or.inr (h1.trans h2)
          · exact hall d x (by simp [hx])
        · obtain ⟨y, hy, hye⟩ := hex d
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · rcases (hd d).2.2 with h1 | h1
            · exact ⟨s, by simp, h1.symm.trans hye⟩
            · exact ⟨t, by simp, h1.symm.trans hye⟩
          · exact ⟨y, by simp [hy], hye⟩
    · simp only [broadcastShape_eq_nil, broadcastShape_eq_cons] at h
      cases hu : (Shape.bcsDispatch bcs1) s t with
      | error e' =>
        simp only [bind, Except.bind, hu, Except.error.injEq] at h
        subst h
        obtain ⟨he, d, h1, h2, h3⟩ := bcs_err s t e' hu
        exact ⟨he, d, s, by simp, t, by simp, h1, h2, h3⟩
      | ok u =>
        simp only [bind, Except.bind, hu] at h
        obtain ⟨he, d, x, hx, x', hx', h1, h2, h3⟩ := (ih u).2 e h
        refine ⟨he, d, ?_⟩
        have hpick : ∀ y ∈ u :: ts, ∃ z ∈ s :: t :: ts, ext z d = ext y d := by
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · rcases ((bcs_ok s t y hu).2 d).2.2 with h4 | h4
            · exact ⟨s, by simp, h4.symm⟩
            · exact ⟨t, by simp, h4.symm⟩
          · exact ⟨y, by simp [hy], rfl⟩
        obtain ⟨z, hz, hze⟩ := hpick x hx
        obtain ⟨z', hz', hze'⟩ := hpick x' hx'
        exact ⟨z, hz, z', hz', by rw [hze]; exact h1, by rw [hze']; exact h2, by rw [hze, hze']; exact h3⟩

/-- `broadcast_shape((3,), (OneTo(1),))` throws `DimensionMismatch` although `OneTo(1)` is a
singleton. -/
theorem bcs1Mixed_3_oneTo1 : bcs1Mixed (.size (i64 3)) (.axis ⟨i64 1⟩) = .error .dimensionMismatch := by
  decide

theorem shapeMixedSingleton_refuted : ¬ ShapeMixedSingleton := by
  intro h
  have := ((h (.size (i64 3)) (.axis ⟨i64 1⟩)).1.mp bcs1Mixed_3_oneTo1).2.1
  exact this (by decide)


/-- All dimension conflicts are rejected, including conflicts after singleton expansion. -/
def ShapeMismatchExactly : Prop :=
  ∀ a b : List I64,
    (Shape.bcsDispatch bcs1) a b = .error .dimensionMismatch ↔
      ∃ d, ext a d ≠ 1 ∧ ext b d ≠ 1 ∧ ext a d ≠ ext b d

theorem shapeMismatchExactly : ShapeMismatchExactly := by
  intro a b
  constructor
  · intro h
    exact (bcs_err a b .dimensionMismatch h).2
  · rintro ⟨d, ha, hb, hab⟩
    cases h : (Shape.bcsDispatch bcs1) a b with
    | error e =>
      have he := (bcs_err a b e h).1
      simpa [he] using h
    | ok out =>
      obtain ⟨_, hall⟩ := bcs_ok a b out h
      have hda := (hall d).1.resolve_left ha
      have hdb := (hall d).2.1.resolve_left hb
      exact False.elim (hab (hda.trans hdb.symm))

private theorem bcs1_comm (a b : I64) : bcs1 a b = bcs1 b a := by
  by_cases ha : a.val = 1
  · by_cases hb : b.val = 1
    · have he : a = b := Subtype.ext (ha.trans hb.symm)
      subst b; rfl
    · simp [bcs1_eq, ha, hb]
  · by_cases hb : b.val = 1
    · simp [bcs1_eq, ha, hb]
    · by_cases he : a.val = b.val
      · have he' : a = b := Subtype.ext he
        subst b; rfl
      · simp [bcs1_eq, ha, hb, he, Ne.symm he]

/-- Integer-size broadcasting is independent of the order of its two arguments. -/
def ShapeCommutative : Prop := ∀ a b : List I64, (Shape.bcsDispatch bcs1) a b = (Shape.bcsDispatch bcs1) b a

theorem shapeCommutative : ShapeCommutative
  | [], [] => rfl
  | [], b :: bs => by simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons]; rw [shapeCommutative [] bs]
  | a :: as, [] => by simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons]; rw [shapeCommutative as []]
  | a :: as, b :: bs => by simp only [bcs_eq_nil_nil, bcs_eq_nil_cons, bcs_eq_cons_nil, bcs_eq_cons_cons]; rw [bcs1_comm a b, shapeCommutative as bs]

end SizesProofs

namespace RangeProofs
open JuliaLean.base.broadcast.Sizes
open JuliaLean.base.broadcast.RangeExamples
open JuliaLean.Ranges

open JuliaLean

namespace RangeAddition
open JuliaLean.base.range

inductive AddOp where | add

local instance : JLength URange I64 where
  length r := do
    let input ← (colon2 (Num.lit (.bit .i64) r.lo.val)
      (Num.lit (.bit .i64) r.hi.val)).mapError Exc.jl
    let n ← (JuliaLean.Ranges.length input).mapError Exc.jl
    (JInt.convert .i64 n.val).mapError Exc.jl

local instance : JFirst URange I64 where
  first r := .ok r.lo

local instance : JStep URange I64 where
  step _ := .ok (i64 1)

local instance : JEq I64 I64 where
  eq a b := a.val == b.val

local instance : JPrint I64 where
  print value := toString value.val

local instance : JScalarOp AddOp I64 I64 I64 where
  scalarOp a b := a + b

local instance : JStepRangeLen3 I64 I64 I64 ResultRng where
  stepRangeLen a s n :=
    (countedRange (.bit .i64) (Num.lit (.bit .i64) a.val)
      (Num.lit (.bit .i64) s.val) (Num.lit (.bit .i64) n.val)).mapError Exc.jl

def ordinalAdd (left right : URange) : JlX ResultRng :=
  rangeop_OrdinalRange_OrdinalRange AddOp left right

end RangeAddition

/-- `r1 .+ r2` for two `UnitRange{Int}`s equals broadcasting over the collected vectors: a
length-1 range is expanded, and only unequal non-singleton lengths throw `DimensionMismatch`. -/
def RangeBroadcastPair : Prop :=
  ∀ r1 r2 : URange,
    match Range.m1198 RangeAddition.ordinalAdd r1 r2, bcAddVectors r1.elems r2.elems with
    | .ok result, .ok values => observeResultRange (t := .i64) result = .ok values
    | .error (.dimensionMismatch _), .error .dimensionMismatch => True
    | _, _ => False

/-- `x .\ r` returns a range for every floating-point colon range `r = a:s:b`. -/
def RangeLdivTotal : Prop :=
  ∀ t : FloatT, ∃ f, bcLdivRange (colonRefT t) = .ok f

/-- `r .- x` for an unsigned `StepRange{UInt64,UInt64}` `r` and an integral `x::Float64` has the
elements `r[i] - x` of `collect(r) .- x` (for small values, where every `Float64` operation is
exact). -/
def RangeUnsignedFloat : Prop :=
  ∀ (a s n : U64) (x : Int) (i : Nat), 1 ≤ s.val → 1 ≤ i → (i : Int) ≤ n.val →
    a.val + (n.val - 1) * s.val < 2 ^ 20 → -2 ^ 20 < x → x < 2 ^ 20 →
    bcSubFloatElem a s n x i = .ok (a.val + ((i : Int) - 1) * s.val - x)

/-- `.-r` for `r::UnitRange{UInt8}` has the elements of `.-collect(r)` (each negated with
wrapping). -/
def RangeNegUnsigned : Prop :=
  ∀ lo hi : U8,
    (do
      let input ← colon2 (Num.lit (.bit .u8) lo.val) (Num.lit (.bit .u8) hi.val)
      let result ← Range.m1179 first last step (fun value => .ok (Num.neg value))
        Num.negate (fun start stop stride => colon3 start stride stop) input
      observeIntegerRange (t := .u8) result) =
      .ok ((urange8Elems lo hi).map (fun v => -v))

/-- `(1:3) .+ (5:5)` throws `DimensionMismatch`; `[1, 2, 3] .+ [5]` is `[6, 7, 8]`. -/
theorem rangePair_example :
    Range.m1198 RangeAddition.ordinalAdd ⟨i64 1, i64 3⟩ ⟨i64 5, i64 5⟩ =
      .error (.dimensionMismatch "argument dimensions must match: length of r1 is 3, length of r2 is 1") ∧
    bcAddVectors (URange.elems ⟨i64 1, i64 3⟩) (URange.elems ⟨i64 5, i64 5⟩) = .ok [i64 6, i64 7, i64 8] := by
  decide

theorem rangeBroadcastPair_refuted : ¬ RangeBroadcastPair := by
  intro h
  have := h ⟨i64 1, i64 3⟩ ⟨i64 5, i64 5⟩
  rw [rangePair_example.1, rangePair_example.2] at this
  exact absurd this (by decide)

/-- `2.0 .\ (0.0:0.5:2.0)` throws `MethodError` (`adjoint(::TwicePrecision{Float64})`). -/
theorem rangeLdiv_example : bcLdivRange (colonRefT .f64) = .error .methodError := by decide

theorem rangeLdivTotal_refuted : ¬ RangeLdivTotal := by
  intro h
  obtain ⟨f, hf⟩ := h .f64
  rw [rangeLdiv_example] at hf
  cases hf

/-- `(UInt(1):UInt(2):UInt(5)) .- 2.0` has first element `2^65 - 1` (printed
`3.6893488147419103e19`) instead of `-1.0`: `imin = 2`, `ref_n = 1`, and `u = 0x1 - 0x2` wraps. -/
theorem rangeUnsignedFloat_example :
    bcSubFloatElem (JInt.lit .u64 1) (JInt.lit .u64 2) (JInt.lit .u64 3) 2 1 = .ok (2 ^ 65 - 1) := by
  decide

theorem rangeUnsignedFloat_refuted : ¬ RangeUnsignedFloat := by
  intro h
  have := h (JInt.lit .u64 1) (JInt.lit .u64 2) (JInt.lit .u64 3) 2 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [rangeUnsignedFloat_example] at this
  exact absurd this (by decide)

/-- `.-(0x00:0x02)` is the empty `0x00:-1:0x01`; `.-collect(0x00:0x02) == [0x00, 0xff, 0xfe]`. -/
theorem rangeNegUnsigned_example :
    (do
      let input ← colon2 (Num.lit (.bit .u8) 0) (Num.lit (.bit .u8) 2)
      let result ← Range.m1179 first last step (fun value => .ok (Num.neg value))
        Num.negate (fun start stop stride => colon3 start stride stop) input
      observeIntegerRange (t := .u8) result) = .ok [] ∧
    (urange8Elems (JInt.lit .u8 0) (JInt.lit .u8 2)).map (fun v => -v) =
      [JInt.lit .u8 0, JInt.lit .u8 255, JInt.lit .u8 254] := by
  decide

theorem rangeNegUnsigned_refuted : ¬ RangeNegUnsigned := by
  intro h
  have := h (JInt.lit .u8 0) (JInt.lit .u8 2)
  have hzero : (JInt.lit .u8 0).val = 0 := by decide
  have htwo : (JInt.lit .u8 2).val = 2 := by decide
  rw [hzero, htwo] at this
  rw [rangeNegUnsigned_example.1, rangeNegUnsigned_example.2] at this
  exact absurd this (by decide)

end RangeProofs

namespace IntegerProofs
open JuliaLean.Ranges

def BroadcastAddLengthPreserved : Prop :=
  ∀ (a b x : Num) (r : Rng) (s : ResultRng),
    colon2 a b = .ok r → (ResultRng.ordinal <$> Range.m1188 first last (fun a b => .ok (Num.add a b)) colon2 r x) = .ok s →
      (resultLength s).map Num.val = (length r).map Num.val

def BroadcastMulElementwise : Prop :=
  ∀ (a b x i : Num) (r : Rng) (s : ResultRng),
    colon2 a b = .ok r → (Range.m1222 first step length (fun a b => .ok (Num.mul a b)) (fun a b => .ok (Num.mul a b)) (fun a s n => countedRange (Num.add a (Num.zero s.ty)).ty a s n) r x) = .ok s →
    i.ty = .bit .i64 → 1 ≤ i.val → i.val ≤ trueCount r →
      (resultGetindex s i).map Num.val = (getindex r i).map (fun y => (Num.mul y x).val)

private def i8 (x : Int) : Num := Num.lit (.bit .i8) x
private def i64 (x : Int) : Num := Num.lit (.bit .i64) x
private def empty127 : Rng := ⟨.unit, i8 127, i8 1, i8 126⟩
private def pair126 : Rng := ⟨.unit, i8 126, i8 1, i8 127⟩

theorem broadcastAddLength_refuted : ¬ BroadcastAddLengthPreserved := by
  intro h
  have bad := h (i8 126) (i8 127) (i8 1) pair126 (.ordinal empty127)
    (by decide) (by decide)
  change (Except.ok (0 : Int) : Jl Int) = .ok 2 at bad
  cases bad

theorem broadcastMulElementwise_refuted : ¬ BroadcastMulElementwise := by
  intro h
  have bad := h (i8 1) (i8 3) (i8 64) (i64 2) ⟨.unit, i8 1, i8 1, i8 3⟩
    (.counted ⟨i8 64, i8 64, i64 3, i64 1, .bit .i8⟩) rfl rfl rfl (by decide) (by decide)
  change (Except.error (JlError.inexactError "Int8") : Jl Int) = .ok (-128) at bad
  cases bad
end IntegerProofs

namespace FloatProofs
open JuliaLean.Float JuliaLean.FloatRanges
def okThen {α : Type} (x : Jl α) (p : α → Prop) : Prop :=
  match x with
  | .ok a => p a
  | .error _ => True

instance {α : Type} (x : Jl α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Decidable (okThen x p) := by
  unfold okThen
  split <;> infer_instance


/-- A range-returning broadcast has the same elements as applying the operator
to each LinRange element, as promised by the broadcast docstring. -/
def LinRangeShiftElementwise : Prop :=
  ∀ (a b x : F64) (n i : I64) (subtract : Bool),
    okThen (Lin.mk' a b n) fun r =>
      okThen ((if subtract then (Range.m1210 Lin.start Lin.stop Lin.len (fun a b => .ok (F64.sub a b)) Lin.mk' r x) else (Range.m1196 Lin.start Lin.stop Lin.len (fun a b => .ok (F64.add a b)) Lin.mk' r x))) fun q =>
        1 ≤ i.val → i.val ≤ r.len.val →
          F64.isequal (q.unsafeGet i)
            (if subtract then F64.sub (r.unsafeGet i) x
             else F64.add (r.unsafeGet i) x) = true

theorem linRangeShiftElementwise_refuted : ¬ LinRangeShiftElementwise := fun h =>
  absurd (h fzero F64.one (dec 2) (i64 7) (i64 2) false) (by decide +kernel)


/-- Broadcast division has the same elements as dividing each original
StepRangeLen element. -/
def StepRangeLenDivElementwise : Prop :=
  ∀ (a s x : F64) (n i : I64),
    okThen (rangeStartStepLength a s n) fun r =>
      okThen ((Range.m1231 SRL.ref SRL.step SRL.length SRL.offset (fun value => .ok value.toF) (fun a b => .ok (F64.div a b)) (fun _ => "Float64") (fun ref scalar => .ok (ref.divF scalar)) (fun step scalar => .ok (step.divF scalar)) (fun _ => SRL.mk') r x)) fun q =>
        1 ≤ i.val → i.val ≤ r.len.val →
          F64.isequal (q.unsafeGet i) (F64.div (r.unsafeGet i) x) = true

theorem stepRangeLenDivElementwise_refuted : ¬ StepRangeLenDivElementwise := fun h =>
  absurd (h fzero (dec 1 4) (dec 3) (i64 6) (i64 6)) (by decide +kernel)


def ScalarMulBroadcast : Prop := ∀ (a s b x : F64) (i : I64),
  okThen (colon a s b) (fun r => okThen (SRL.scalarMul x r) (fun p =>
    okThen ((Range.m1216 SRL.ref SRL.step SRL.length SRL.offset (fun value => .ok value.toF) (fun a b => .ok (F64.mul a b)) (fun _ => "Float64") (fun scalar ref => .ok (ref.mulF scalar)) (fun scalar step => .ok (step.mulF scalar)) (fun _ => SRL.mk') r x)) (fun q => 1 ≤ i.val → i.val ≤ r.len.val →
      F64.isequal (p.unsafeGet i) (q.unsafeGet i) = true)))

theorem scalarMulBroadcast_refuted : ¬ ScalarMulBroadcast := fun h =>
  absurd (h fzero (dec 1 10) (dec 3 10) (dec 3) (i64 4)) (by decide +kernel)

end FloatProofs
namespace AliasProofs
open JuliaLean.BroadcastViews
abbrev InBounds (dims : List Nat) (ps : List (List Int)) : Prop :=
  ps.all (fun p => p.length == dims.length && (p.zip dims).all (fun q => 1 ≤ q.1 && q.1 ≤ (q.2 : Int))) = true

def SelfAssignFresh : Prop :=
  ∀ (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int),
    mem.length = dims.foldr (· * ·) 1 → InBounds dims (positions I) →
    AliasExamples.bcSelfAdd dims mem I c = freshSelfAdd dims mem I c

theorem selfAssignFresh_refuted : ¬ SelfAssignFresh := by
  intro h
  have bad := h [3] [10, 20, 30] [.ints [1, 1, 2]] 1 (by decide) (by decide)
  have actual : AliasExamples.bcSelfAdd [3] [10,20,30] [.ints [1,1,2]] 1 = [12,21,30] := by decide
  have expected : freshSelfAdd [3] [10,20,30] [.ints [1,1,2]] 1 = [11,21,30] := by decide
  rw [actual, expected] at bad
  contradiction
end AliasProofs


namespace AxisRemapProofs

def expectedCoordinates (axes : List Index.Axis) (indices : List Int) : List Int :=
  axes.mapIdx fun i axis =>
    if axis.values.length = 1 then axis.first else indices[i]?.getD axis.first

theorem expected_empty (axis : Index.Axis) (axes : List Index.Axis) :
    expectedCoordinates (axis :: axes) [] = axis.first :: expectedCoordinates axes [] := by
  simp [expectedCoordinates, List.mapIdx_cons]

theorem expected_cons (axis : Index.Axis) (axes : List Index.Axis) (i : Int) (indices : List Int) :
    expectedCoordinates (axis :: axes) (i :: indices) =
      (if axis.values.length = 1 then axis.first else i) :: expectedCoordinates axes indices := by
  simp [expectedCoordinates, List.mapIdx_cons]

theorem remap_nil (indices : List Int) : Index.remapAxes [] indices = .ok [] := by
  cases indices <;> rfl

theorem remap_empty (axis : Index.Axis) (axes : List Index.Axis) :
    Index.remapAxes (axis :: axes) [] =
      (do let rest ← Index.remapAxes axes []; pure (axis.first :: rest)) := by
  simp only [Index.remapAxes]
  rw [Index.m589.eq_def]
  all_goals cases axes <;> rfl

theorem remap_cons (axis : Index.Axis) (axes : List Index.Axis) (i : Int) (indices : List Int) :
    Index.remapAxes (axis :: axes) (i :: indices) =
      (do let rest ← Index.remapAxes axes indices
          pure ((if axis.values.length = 1 then axis.first else i) :: rest)) := by
  simp only [Index.remapAxes]
  rw [Index.m587.eq_def]
  all_goals cases axes <;> cases indices <;> rfl

theorem remap_exact (axes : List Index.Axis) (indices : List Int) :
    Index.remapAxes axes indices = .ok (expectedCoordinates axes indices) := by
  induction axes generalizing indices with
  | nil => simp [remap_nil, expectedCoordinates]
  | cons axis axes ih =>
    cases indices with
    | nil =>
      rw [remap_empty, ih [], expected_empty]
      rfl
    | cons i indices =>
      rw [remap_cons, ih indices, expected_cons]
      rfl

/-- Remapping keeps each ordinary input coordinate, replaces every singleton coordinate by
its axis's first coordinate, fills missing coordinates with those first coordinates, and
discards coordinates beyond the source rank. The source's result packing is retained. -/
def AxisCoordinateProjection : Prop :=
  ∀ {A : Type} (axes : A → List Index.Axis) (array : A),
    (∀ indices : List Int,
      Index.m585 axes array indices = .ok (Index.toIndex (expectedCoordinates (axes array) indices))) ∧
    (∀ index : Int,
      Index.m586 axes array index = .ok (Index.toIndex (expectedCoordinates (axes array) [index])))

theorem axisCoordinateProjection : AxisCoordinateProjection := by
  intro A axes array
  constructor
  · intro indices
    simp [Index.m585, remap_exact, Functor.map, Except.map]
  · intro index
    simp [Index.m586, remap_exact, Functor.map, Except.map]

end AxisRemapProofs

namespace KeepRemapProofs

def expected (indices : List Int) (keep : List Bool) (defaults : List Int) : List Int :=
  List.zipWith (fun (entry : Int × Bool) default => if entry.2 then entry.1 else default)
    (indices.zip keep) defaults

theorem keep_no_indices (keep : List Bool) (defaults : List Int) :
    Index.remapKeep [] keep defaults = .ok [] := by
  cases keep <;> rfl

theorem keep_no_flags (indices : List Int) (defaults : List Int) :
    Index.remapKeep indices [] defaults = .ok [] := by
  cases indices <;> rfl

theorem keep_missing (i : Int) (indices : List Int) (flag : Bool) (keep : List Bool) :
    Index.remapKeep (i :: indices) (flag :: keep) [] = .error (.julia .boundsError) := rfl

theorem keep_cons (i : Int) (indices : List Int) (flag : Bool) (keep : List Bool)
    (default : Int) (defaults : List Int) :
    Index.remapKeep (i :: indices) (flag :: keep) (default :: defaults) =
      (do let rest ← Index.remapKeep indices keep defaults
          pure ((if flag then i else default) :: rest)) := by
  simp only [Index.remapKeep]
  rw [Index.m598.eq_def]
  all_goals cases indices <;> cases keep <;> cases defaults <;> rfl

theorem keep_exact (indices : List Int) (keep : List Bool) (defaults : List Int) :
    Index.remapKeep indices keep defaults =
      if min indices.length keep.length ≤ defaults.length
      then .ok (expected indices keep defaults)
      else .error (.julia .boundsError) := by
  induction indices generalizing keep defaults with
  | nil => simp [keep_no_indices, expected]
  | cons i indices ih =>
    cases keep with
    | nil => simp [keep_no_flags, expected]
    | cons flag keep =>
      cases defaults with
      | nil => simp [keep_missing, expected]
      | cons default defaults =>
        rw [keep_cons, ih keep defaults]
        have hsize :
            min (i :: indices).length (flag :: keep).length ≤ (default :: defaults).length ↔
              min indices.length keep.length ≤ defaults.length := by
          simp only [List.length_cons]
          omega
        simp only [hsize]
        by_cases h : min indices.length keep.length ≤ defaults.length
        · simp [h, expected, bind, Except.bind, pure, Except.pure]
        · simp [h, bind, Except.bind]

/-- Keep/default remapping truncates only at the end of the input or keep tuple. Every
retained position requires a default, even when its keep flag is true, because Julia's
ifelse evaluates both inputs. Present defaults select exactly the requested coordinates. -/
def KeepCoordinateProjection : Prop :=
  ∀ (indices : List Int) (keep : List Bool) (defaults : List Int),
    Index.m593 indices keep defaults =
      if min indices.length keep.length ≤ defaults.length
      then .ok (Index.toIndex (expected indices keep defaults))
      else .error (.julia .boundsError)

theorem keepCoordinateProjection : KeepCoordinateProjection := by
  intro indices keep defaults
  simp only [Index.m593, keep_exact]
  split <;> rfl

def nativeInt (value : Int) : Index.Result JInt64 :=
  (JInt.convert .i64 value).mapError JuliaLean.base.tuple.TupleError.julia

def cartesianConstructor (values : List Int) : Index.Result Index.Index :=
  (JuliaLean.base.multidimensional.cartesianVarargs
    (JuliaLean.base.multidimensional.cartesianTuple
      (JuliaLean.base.multidimensional.cartesianInner nativeInt)) values).map
    (fun coordinates => .cartesian (coordinates.map (fun coordinate => coordinate.val)))

theorem nativeInt_i64 (value : JInt64) : nativeInt value.val = .ok value := by
  simp [nativeInt, JInt.convert, value.property, Except.mapError]

theorem convertInt_i64 (value : JInt64) : Index.convertInt value.val = .ok value := by
  simp [Index.convertInt, JInt.convert, value.property]

theorem nativeMap_i64 (values : List JInt64) :
    (values.map (fun value => value.val)).mapM nativeInt = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.map_cons, List.mapM_cons, nativeInt_i64, ih, bind, Except.bind, pure, Except.pure]

theorem cartesian_i64 (values : List JInt64) :
    cartesianConstructor (values.map (fun value => value.val)) =
      .ok (.cartesian (values.map (fun value => value.val))) := by
  simp only [cartesianConstructor, JuliaLean.base.multidimensional.cartesianVarargs,
    JuliaLean.base.multidimensional.cartesianTuple, JuliaLean.base.multidimensional.cartesianInner]
  rw [nativeMap_i64]
  rfl

/-- A CartesianIndex{1} delegates to the numeric overloads: one flag yields a scalar,
two or more flags yield two Cartesian coordinates, and no flags yield rank zero. -/
def NumericIndexPacking : Prop :=
  (∀ (value default : Int) (flag : Bool) (defaults : List Int),
    Index.m594 cartesianConstructor value [flag] (default :: defaults) =
      .ok (.scalar (if flag then value else default))) ∧
  (∀ (value first second : JInt64) (flag next : Bool)
      (keep : List Bool) (defaults : List Int),
    Index.m594 cartesianConstructor value.val (flag :: next :: keep)
      (first.val :: second.val :: defaults) =
        .ok (.cartesian [if flag then value.val else first.val, second.val])) ∧
  (∀ (value : Int) (defaults : List Int),
    Index.m594 cartesianConstructor value [] defaults = .ok (.cartesian []))

theorem numericIndexPacking : NumericIndexPacking := by
  refine ⟨?_, ?_, ?_⟩
  · intro value default flag defaults
    cases flag <;>
      simp [Index.m594, Index.numericIndex, Index.m596, JuliaLean.base.tuple.getfield,
        bind, Except.bind, pure, Except.pure]
  · intro value first second flag next keep defaults
    cases flag with
    | false =>
      have hc := cartesian_i64 [first, second]
      simp only [List.map_cons, List.map_nil] at hc
      simp [Index.m594, Index.numericIndex, Index.m595, JuliaLean.base.tuple.getfield,
        convertInt_i64, hc, Except.mapError, bind, Except.bind, pure, Except.pure]
    | true =>
      have hc := cartesian_i64 [value, second]
      simp only [List.map_cons, List.map_nil] at hc
      simp [Index.m594, Index.numericIndex, Index.m595, JuliaLean.base.tuple.getfield,
        convertInt_i64, hc, Except.mapError, bind, Except.bind, pure, Except.pure]
  · intro value defaults
    rfl

/-- Numeric remapping performs eager default access and eager Int narrowing. A true keep
flag cannot suppress a missing default or a failed conversion of an unused branch. -/
def NumericIndexEagerErrors : Prop :=
  (∀ (value : Int) (flag : Bool),
    Index.m594 cartesianConstructor value [flag] [] = .error (.julia .boundsError)) ∧
  (∀ (value : Int) (flag next : Bool) (keep : List Bool) (defaults : List Int),
    ¬ (IntTy.i64.min ≤ value ∧ value ≤ IntTy.i64.max) →
    Index.m594 cartesianConstructor value (flag :: next :: keep) defaults =
      .error (.julia (.inexactError "Int64"))) ∧
  (∀ (value : JInt64) (default : Int) (flag next : Bool)
      (keep : List Bool) (defaults : List Int),
    ¬ (IntTy.i64.min ≤ default ∧ default ≤ IntTy.i64.max) →
    Index.m594 cartesianConstructor value.val (flag :: next :: keep) (default :: defaults) =
      .error (.julia (.inexactError "Int64")))

theorem numericIndexEagerErrors : NumericIndexEagerErrors := by
  refine ⟨?_, ?_, ?_⟩
  · intro value flag
    rfl
  · intro value flag next keep defaults hwide
    simp [Index.m594, Index.numericIndex, Index.m595, JuliaLean.base.tuple.getfield,
      Index.convertInt, JInt.convert, hwide, IntTy.name, Except.mapError, bind, Except.bind]
  · intro value default flag next keep defaults hwide
    simp [Index.m594, Index.numericIndex, Index.m595, JuliaLean.base.tuple.getfield,
      convertInt_i64, JInt.convert, Index.convertInt, value.property, hwide, IntTy.name,
      Except.mapError, bind, Except.bind]

end KeepRemapProofs

namespace Elementwise

theorem indexer_nil : Index.newIndexer [] = .ok ([], []) := rfl

theorem indexer_cons (axis : Index.Axis) (axes : List Index.Axis) :
    Index.newIndexer (axis :: axes) =
      (do let rest ← Index.newIndexer axes
          pure ((axis.values.length ≠ 1) :: rest.1, Index.axisFirst axis :: rest.2)) := by
  simp only [Index.newIndexer]
  rw [Index.m609.eq_def]
  all_goals cases axes <;> rfl

theorem indexer_values (axes : List Index.Axis) :
    Index.newIndexer axes = .ok
      (axes.map (fun axis => decide (axis.values.length ≠ 1)), axes.map Index.axisFirst) := by
  induction axes with
  | nil => rfl
  | cons axis axes ih =>
    rw [indexer_cons, ih]
    rfl

/-- Precomputed indexing flags keep exactly nonsingleton coordinates, and every default
is the first coordinate of the corresponding source axis. -/
def IndexerCoordinates : Prop :=
  ∀ axes : List Index.Axis,
    Index.m607 axes = .ok
      (axes.map (fun axis => decide (axis.values.length ≠ 1)), axes.map Index.axisFirst)

theorem indexerCoordinates : IndexerCoordinates := by
  intro axes
  exact indexer_values axes

private theorem gather_map {A I V : Type} (getindex : A → I → V) (args : List A) (i : I) :
    Index.gather getindex args i = args.map (fun a => getindex a i) := by
  induction args with
  | nil => rfl
  | cons a rest ih => simp [Index.gather, ih]

/-- Every broadcast argument contributes its own value at the output index. -/
def ElementwiseApplication : Prop :=
  ∀ {A I V : Type} (getindex : A → I → V) (bc : Index.EvalBroadcasted A V) (i : I),
    Index.m675 getindex bc i = bc.f (bc.args.map (fun arg => getindex arg i))

theorem elementwiseApplication : ElementwiseApplication := by
  intro A I V getindex bc i
  exact congrArg bc.f (gather_map getindex bc.args i)

/-- Changing an argument away from the current index cannot change that output element. -/
def Locality : Prop :=
  ∀ {A I V : Type} (left right : A → I → V) (bc : Index.EvalBroadcasted A V) (i : I),
    (∀ arg ∈ bc.args, left arg i = right arg i) →
      Index.m675 left bc i = Index.m675 right bc i

theorem locality : Locality := by
  intro A I V left right bc i h
  rw [elementwiseApplication, elementwiseApplication]
  congr 1
  exact List.map_congr_left h

/-- Preparing arguments preserves their number and order. -/
def PreprocessArguments : Prop :=
  ∀ {D A B : Type} (prepare : D → A → B) (dest : D) (args : List A),
    Material.preprocessArgs prepare dest args = args.map (prepare dest)

theorem preprocessArguments : PreprocessArguments := by
  intro D A B prepare dest args
  induction args with
  | nil => rfl
  | cons a rest ih => simp [Material.preprocessArgs, ih]

/-- Index precomputation uses one entry for each source dimension. -/
private def IndexerRankReference : Prop :=
  ∀ axes : List Index.Axis, ∀ keep defaults,
    Index.newIndexer axes = .ok (keep, defaults) →
      keep.length = axes.length ∧ defaults.length = axes.length

private theorem indexerRankReference : IndexerRankReference := by
  intro axes
  induction axes with
  | nil =>
    intro keep defaults h
    simp [indexer_nil, indexer_cons] at h
    cases h.1; cases h.2
    exact ⟨rfl, rfl⟩
  | cons a rest ih =>
    intro keep defaults h
    cases hr : Index.newIndexer rest with
    | error e => simp [indexer_nil, indexer_cons, hr, Functor.map, Except.map] at h
    | ok p =>
      obtain ⟨k, d⟩ := p
      have hi := ih k d hr
      simp [indexer_nil, indexer_cons, hr, Functor.map, Except.map] at h
      cases h.1; cases h.2
      simpa using hi

/-- With no expanded dimensions, every coordinate is preserved. -/
private def UnexpandedReference : Prop :=
  ∀ indices : List Int, Index.remapKeep indices (indices.map (fun _ => true)) indices = .ok indices

private theorem unexpandedReference : UnexpandedReference := by
  intro indices
  induction indices with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons]
    rw [KeepRemapProofs.keep_cons, ih]
    rfl

/-- Scalar-only input axes require a scalar result, regardless of how many arguments there are. -/
private def ScalarRankReference : Prop :=
  ∀ args : List Lazy.ArgRank,
    (∀ arg ∈ args, arg = .other 0) → Lazy.maxNdim args = 0

private theorem scalarRankReference : ScalarRankReference := by
  intro args h
  induction args with
  | nil => rfl
  | cons a rest ih =>
    have ha := h a (by simp)
    have ht : ∀ arg ∈ rest, arg = .other 0 := fun arg hm => h arg (by simp [hm])
    rw [RankProofs.consRank]
    simp [Lazy.argRank, ha, ih ht]


/-- Source `shapeindexer` returns one keep flag and one default coordinate per axis. -/
def IndexerRank : Prop :=
  ∀ axes : List Index.Axis, ∀ keep defaults,
    Index.m607 axes = .ok (keep, defaults) →
      keep.length = axes.length ∧ defaults.length = axes.length

theorem indexerRank : IndexerRank := by
  intro axes keep defaults h
  exact indexerRankReference axes keep defaults h

/-- Coordinate-vector observation, independent of scalar versus Cartesian result packing. -/
private def coordinates : Index.Index → List Int
  | .scalar i => [i]
  | .cartesian indices => indices

private theorem coordinates_toIndex (indices : List Int) :
    coordinates (Index.toIndex indices) = indices := by
  cases indices with
  | nil => rfl
  | cons i rest => cases rest <;> rfl

def UnexpandedCoordinates : Prop :=
  ∀ indices : List Int,
    (Index.m593 indices (indices.map (fun _ => true)) indices).map coordinates = .ok indices

theorem unexpandedCoordinates : UnexpandedCoordinates := by
  intro indices
  simp only [Index.m593]
  rw [unexpandedReference indices]
  change Except.ok (coordinates (Index.toIndex indices)) = Except.ok indices
  rw [coordinates_toIndex]

/-- The recursive `_maxndims` branch preserves zero-dimensional scalar-only input. -/
def ScalarResultRank : Prop :=
  ∀ (head : Lazy.ArgRank) (rest : List Lazy.ArgRank),
    head = .other 0 → (∀ arg ∈ rest, arg = .other 0) → Lazy.m275 head rest = 0

theorem scalarResultRank : ScalarResultRank := by
  intro head rest hh hr
  rw [RankProofs.recursiveRank]
  simp [Lazy.argRank, hh, scalarRankReference rest hr]
end Elementwise

namespace Mutation

/-! Proof-internal storage reference. `runAssignment_eq` proves its equivalence to the
source copy loop; these callback-parametric lemmas are not registry specifications. -/
private def referenceWriteAll {D I V : Type} (setindex : D → I → V → D) (getindex : D → I → V) : D → List I → D
  | dest, [] => dest
  | dest, index :: rest => referenceWriteAll setindex getindex (setindex dest index (getindex dest index)) rest


/-- Pointwise copying writes only visited coordinates. -/
def UntouchedWrite : Prop :=
  ∀ {V : Type} (memory : Nat → V) (read : (Nat → V) → Nat → V)
      (indices : List Nat) (j : Nat),
    j ∉ indices →
      referenceWriteAll (fun m i v k => if k = i then v else m k) read memory indices j = memory j

theorem untouchedWrite : UntouchedWrite := by
  intro V memory read indices
  induction indices generalizing memory with
  | nil => simp [referenceWriteAll]
  | cons i rest ih =>
    intro j h
    have hj : j ≠ i := fun he => h (by simp [he])
    have hr : j ∉ rest := fun hm => h (by simp [hm])
    simp only [referenceWriteAll]
    rw [ih _ j hr]
    simp [hj]

/-- Copying a precomputed source produces its value at every visited destination. -/
def SnapshotWrite : Prop :=
  ∀ {V : Type} (memory : Nat → V) (source : Nat → V) (indices : List Nat) (j : Nat),
    j ∈ indices →
      referenceWriteAll (fun m i v k => if k = i then v else m k)
        (fun _ i => source i) memory indices j = source j

theorem snapshotWrite : SnapshotWrite := by
  intro V memory source indices
  induction indices generalizing memory with
  | nil => simp
  | cons i rest ih =>
    intro j h
    by_cases hr : j ∈ rest
    · exact ih _ j hr
    · have hj : j = i := by simpa [hr] using h
      subst j
      rw [referenceWriteAll, untouchedWrite _ _ _ _ hr]
      simp


/-- The ordinary storage instance of the source copy loop, retaining the current memory
between a read and the following write. -/
abbrev runAssignment {V : Type} (read : (Nat → V) → Nat → V) (memory : Nat → V)
    (indices : List Nat) : Except Empty (Unit × (Nat → V)) :=
  Material.copyLoop
    (fun (_ : Unit) i m => .ok (read m i, m))
    (fun (_ : Unit) i value m => .ok ((), fun k => if k = i then value else m k))
    () () indices memory

private theorem runAssignment_eq {V : Type} (read : (Nat → V) → Nat → V)
    (memory : Nat → V) (indices : List Nat) :
    runAssignment read memory indices =
      .ok ((), referenceWriteAll (fun m i v k => if k = i then v else m k) read memory indices) := by
  induction indices generalizing memory with
  | nil => rfl
  | cons i rest ih =>
    change runAssignment read (fun k => if k = i then read memory i else memory k) rest = _
    exact ih _

/-- The actual source loop leaves every unselected memory location unchanged. -/
def UntouchedStorage : Prop :=
  ∀ {V : Type} (memory : Nat → V) (read : (Nat → V) → Nat → V)
      (indices : List Nat) (result : Nat → V) (j : Nat),
    j ∉ indices → runAssignment read memory indices = .ok ((), result) → result j = memory j

theorem untouchedStorage : UntouchedStorage := by
  intro V memory read indices result j hj h
  rw [runAssignment_eq] at h
  have he := (Prod.mk.inj (Except.ok.inj h)).2
  rw [← he]
  exact untouchedWrite memory read indices j hj

/-- Copying from a separate snapshot writes the pre-assignment value, including
when the destination index appears more than once. -/
def SnapshotAssignment : Prop :=
  ∀ {V : Type} (memory : Nat → V) (source : Nat → V)
      (indices : List Nat) (result : Nat → V) (j : Nat),
    j ∈ indices → runAssignment (fun _ i => source i) memory indices = .ok ((), result) →
      result j = source j

theorem snapshotAssignment : SnapshotAssignment := by
  intro V memory source indices result j hj h
  rw [runAssignment_eq] at h
  have he := (Prod.mk.inj (Except.ok.inj h)).2
  rw [← he]
  exact snapshotWrite memory source indices j hj


private theorem selfWrite_once {V : Type} (f : V → V) (memory : Nat → V)
    (indices : List Nat) (distinct : indices.Nodup) (j : Nat) (hj : j ∈ indices) :
    referenceWriteAll (fun m i v k => if k = i then v else m k)
      (fun m i => f (m i)) memory indices j = f (memory j) := by
  induction indices generalizing memory with
  | nil => simp at hj
  | cons i rest ih =>
    obtain ⟨hi, hrest⟩ := List.nodup_cons.mp distinct
    by_cases hr : j ∈ rest
    · have hji : j ≠ i := by intro he; subst j; exact hi hr
      rw [referenceWriteAll]
      rw [ih _ hrest hr]
      simp [hji]
    · have hji : j = i := by simpa [hr] using hj
      subst j
      rw [referenceWriteAll, untouchedWrite _ _ _ _ hi]
      simp

/-- Ordinary non-repeating destinations read each original element exactly once. -/
def SelfAssignmentDistinct : Prop :=
  ∀ {V : Type} (memory : Nat → V) (f : V → V) (indices : List Nat)
      (result : Nat → V) (j : Nat),
    indices.Nodup → j ∈ indices →
    runAssignment (fun m i => f (m i)) memory indices = .ok ((), result) →
      result j = f (memory j)

theorem selfAssignmentDistinct : SelfAssignmentDistinct := by
  intro V memory f indices result j hd hj h
  rw [runAssignment_eq] at h
  have he := (Prod.mk.inj (Except.ok.inj h)).2
  rw [← he]
  exact selfWrite_once f memory indices hd j hj
end Mutation


open JuliaLean.Registry
def entries : List Entry := [
  { id := "broadcast-numeric-index-packing", juliaFile := "base/broadcast.jl",
    juliaFns := ["newindex(::CartesianIndex{1},keep,Idefault)@594",
      "newindex(::Integer,::Tuple,idefault)@595", "newindex(::Integer,::Tuple{Bool},idefault)@596",
      "newindex(::Integer,::Tuple{},idefault)@597"],
    statement := "A one-dimensional Cartesian input selects the numeric overload: one keep flag returns the selected scalar, the generic keep tuple returns two correctly selected Cartesian coordinates, and an empty keep tuple returns a zero-dimensional CartesianIndex.",
    source := "base/broadcast.jl:594-597; numeric index specialization and CartesianIndex construction", status := .proven,
    prop := ``KeepRemapProofs.NumericIndexPacking, thm := some ``KeepRemapProofs.numericIndexPacking },
  { id := "broadcast-numeric-index-eager-errors", juliaFile := "base/broadcast.jl",
    juliaFns := ["newindex(::CartesianIndex{1},keep,Idefault)@594",
      "newindex(::Integer,::Tuple,idefault)@595", "newindex(::Integer,::Tuple{Bool},idefault)@596"],
    statement := "Numeric index remapping reports missing defaults and Int64 narrowing errors even when the keep flag selects the other branch; input conversion precedes default conversion in the generic tuple overload.",
    source := "base/broadcast.jl:594-596; eager ifelse and Int conversion error order", status := .proven,
    prop := ``KeepRemapProofs.NumericIndexEagerErrors, thm := some ``KeepRemapProofs.numericIndexEagerErrors },
  { id := "broadcast-keep-coordinate-projection", juliaFile := "base/broadcast.jl",
    juliaFns := ["newindex(::CartesianIndex,keep,Idefault)@593", "_newindex(I,keep,Idefault)@598",
      "_newindex(I,::Tuple{},Idefault)@600", "_newindex(::Tuple{},keep,Idefault)@601",
      "_newindex(::Tuple{},::Tuple{},Idefault)@602"],
    statement := "Keep/default index remapping selects the correct coordinate at every retained position, truncates only at the input or keep rank, and raises BoundsError exactly when a required default is absent, including defaults for retained coordinates.",
    source := "base/broadcast.jl:593-602; tuple truncation and eager ifelse indexing", status := .proven,
    prop := ``KeepRemapProofs.KeepCoordinateProjection, thm := some ``KeepRemapProofs.keepCoordinateProjection },
  { id := "broadcast-axis-coordinate-projection", juliaFile := "base/broadcast.jl",
    juliaFns := ["newindex(arg,::CartesianIndex)@585", "newindex(arg,::Integer)@586",
      "_newindex(::Tuple,::Tuple)@587", "_newindex(::Tuple{},::Tuple)@588",
      "_newindex(::Tuple,::Tuple{})@589", "_newindex(::Tuple{},::Tuple{})@590"],
    statement := "Index remapping preserves nonsingleton coordinates, replaces singleton coordinates by their axis starts, fills missing coordinates by axis starts, and truncates extra coordinates to the source rank.",
    source := "base/broadcast.jl:577-590; broadcast coordinate remapping", status := .proven,
    prop := ``AxisRemapProofs.AxisCoordinateProjection, thm := some ``AxisRemapProofs.axisCoordinateProjection },
  { id := "broadcast-every-argument-validated", juliaFile := "base/broadcast.jl",
    juliaFns := ["check_broadcast_axes(shp,A,B...)@563", "check_broadcast_axes(shp,A)@561"],
    statement := "Variadic broadcast shape validation accepts exactly when every supplied array is compatible with the destination; the recursive check skips no argument.",
    source := "base/broadcast.jl:546-564; check all arguments against the destination shape", status := .proven,
    prop := ``ValidationProofs.EveryArgumentValidated, thm := some ``ValidationProofs.everyArgumentValidated },
  { id := "broadcast-indexer-coordinates", juliaFile := "base/broadcast.jl",
    juliaFns := ["shapeindexer(ax)@607", "_newindexer(::Tuple{})@608", "_newindexer(::Tuple)@609"],
    statement := "Indexer precomputation keeps exactly nonsingleton coordinates and uses the first coordinate of each source axis as its corresponding default.",
    source := "base/broadcast.jl:606-613; singleton index remapping", status := .proven,
    prop := ``Elementwise.IndexerCoordinates, thm := some ``Elementwise.indexerCoordinates },
  { id := "broadcast-axis-combination", juliaFile := "base/broadcast.jl",
    juliaFns := ["_bcs1(axis,axis)@534", "_bcsm(axis,axis)@536", "axistype(::T,::T)@542"],
    statement := "Combining same-type axes rejects exactly unequal nonsingleton axes and otherwise retains a complete input axis with the length required by every nonsingleton input.",
    source := "base/broadcast.jl:506-518, 534-542; axis singleton expansion", status := .proven,
    prop := ``TypedShapeProofs.AxisCombination, thm := some ``TypedShapeProofs.axisCombination },
  { id := "broadcast-axis-shape-rank", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcast_shape(::Tuple,::Tuple,::Tuple...)@522", "_bcs(::Tuple,::Tuple)@527",
      "_bcs1(axis,axis)@534", "_bcsm(axis,axis)@536", "axistype(::T,::T)@542"],
    statement := "Successful broadcast shape combination of same-type axes retains exactly the largest argument rank.",
    source := "base/broadcast.jl:506-542; maximum output dimensionality", status := .proven,
    prop := ``TypedShapeProofs.AxisShapeRank, thm := some ``TypedShapeProofs.axisShapeRank },
  { id := "broadcast-numeric-compatibility", juliaFile := "base/broadcast.jl",
    juliaFns := ["_bcsm(axis,::Number)@537", "_bcsm(::Number,::Number)@538"],
    statement := "Numeric extent compatibility accepts exactly an equal extent or a singleton right extent; a numeric right extent compared against an axis must be singleton.",
    source := "base/broadcast.jl:506-518, 537-538; numeric singleton expansion", status := .proven,
    prop := ``TypedShapeProofs.NumericCompatibility, thm := some ``TypedShapeProofs.numericCompatibility },
  { id := "broadcast-integer-axis-compatibility", juliaFile := "base/broadcast.jl",
    juliaFns := ["_bcs1(::Integer,axis)@532", "_bcs1(axis,::Integer)@533"],
    statement := "Combining an integer extent with an axis succeeds exactly for a singleton extent or an axis starting at one and ending at that extent, retains the complete axis, and otherwise raises DimensionMismatch in either argument order.",
    source := "base/broadcast.jl:506-518, 532-533; integer versus axis singleton expansion", status := .proven,
    prop := ``TypedShapeProofs.IntegerAxisCompatibility, thm := some ``TypedShapeProofs.integerAxisCompatibility },
  { id := "broadcast-typed-integer-dimension-join", juliaFile := "base/broadcast.jl",
    juliaFns := ["_bcs1(::Integer,::Integer)@531"],
    statement := "Integer singleton expansion accepts exactly equal or singleton dimensions across all pairs of bit-integer types and preserves an input's value and integer type.",
    source := "base/broadcast.jl:506-518, 531; singleton-expansion compatibility", status := .proven,
    prop := ``TypedShapeProofs.IntegerDimensionJoin, thm := some ``TypedShapeProofs.integerDimensionJoin },
  { id := "broadcast-typed-integer-shape-rank", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcast_shape(::Tuple,::Tuple,::Tuple...)@522", "_bcs(::Tuple,::Tuple)@527",
      "_bcs1(::Integer,::Integer)@531"],
    statement := "Successful broadcast shape combination of integer dimensions retains exactly the largest argument rank, including shapes that mix different integer types.",
    source := "base/broadcast.jl:506-518, 522-531; maximum output dimensionality", status := .proven,
    prop := ``TypedShapeProofs.IntegerShapeRank, thm := some ``TypedShapeProofs.integerShapeRank },
  { id := "broadcast-nested-boolean-short-circuit", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(::AndAnd,a,::Broadcasted)@199",
      "broadcasted(::OrOr,a,::Broadcasted)@208", "flatten(::Broadcasted)@346",
      "broadcasted(f,arg1,args...)@1409", "broadcasted(::BroadcastStyle,f,args...)@1420"],
    statement := "Nested Boolean broadcasting suppresses evaluation exactly on the short-circuit branch, preserves the nested evaluator's result or error on the other branch, and retains every flattened argument.",
    source := "base/broadcast.jl:194-213; dotted Boolean short-circuit evaluation", status := .proven,
    prop := ``BooleanProofs.ShortCircuitNested, thm := some ``BooleanProofs.shortCircuitNested },
  { id := "broadcast-flatness-exact", juliaFile := "base/broadcast.jl",
    juliaFns := ["isflat(::Broadcasted)@364", "_isflat(::NestedTuple)@365",
      "_isflat(::Tuple)@366", "_isflat(::Tuple{})@367"],
    statement := "The flatness predicate accepts exactly argument tuples with no nested Broadcasted wrapper.",
    source := "base/broadcast.jl:346, 364-367; flat versus nested argument invariant", status := .proven,
    prop := ``FlattenProofs.FlatnessExactly, thm := some ``FlattenProofs.flatnessExactly },
  { id := "broadcast-concatenated-leaf-order", juliaFile := "base/broadcast.jl",
    juliaFns := ["cat_nested(::Broadcasted)@369", "cat_nested_args(::Tuple{})@370",
      "cat_nested_args(::Tuple{Any})@371", "cat_nested_args(::Tuple)@372", "cat_nested(a)@373"],
    statement := "Concatenating nested broadcast arguments retains every leaf in depth-first argument order.",
    source := "base/broadcast.jl:346-361, 369-373; flattening concatenates nested argument tuples", status := .proven,
    prop := ``FlattenProofs.ConcatenatedLeafOrder, thm := some ``FlattenProofs.concatenatedLeafOrder },
  { id := "broadcast-flatten-preserves-leaves", juliaFile := "base/broadcast.jl",
    juliaFns := ["flatten(::Broadcasted)@346", "cat_nested(::Broadcasted)@369",
      "cat_nested_args(::Tuple)@372"],
    statement := "Flattening removes all nested argument wrappers, retains every leaf in its original depth-first order, and preserves the outer style and output axes.",
    source := "base/broadcast.jl:346-361; flatten preserves lazy broadcast inputs and metadata", status := .proven,
    prop := ``FlattenProofs.FlattenPreservesLeaves, thm := some ``FlattenProofs.flattenPreservesLeaves },
  { id := "broadcast-leaf-picker-correct", juliaFile := "base/broadcast.jl",
    juliaFns := ["_make_makeargs1(_,n)@398", "Pick{N}(::Tuple)@395"],
    statement := "A generated leaf selector reads its one-based tuple position and raises BoundsError for invalid positions.",
    source := "base/broadcast.jl:395-398; Pick selects its stored argument position", status := .proven,
    prop := ``FlattenProofs.LeafPickerCorrect, thm := some ``FlattenProofs.leafPickerCorrect },
  { id := "broadcast-selector-arity", juliaFile := "base/broadcast.jl",
    juliaFns := ["make_makeargs(::Tuple)@382", "_make_makeargs(::Tuple,n)@386",
      "_make_makeargs(::Tuple{},n)@391", "_make_makeargs1(_,n)@398", "_make_makeargs1(::Broadcasted,n)@400"],
    statement := "The selector builder produces one evaluator for each original broadcast argument, including nested arguments.",
    source := "base/broadcast.jl:350-357, 382-405; selector tuple cardinality invariant", status := .proven,
    prop := ``FlattenProofs.SelectorArity, thm := some ``FlattenProofs.selectorArity },
  { id := "broadcast-prepared-argument-arity", juliaFile := "base/broadcast.jl",
    juliaFns := ["prepare_args(::Tuple,::Tuple)@407", "prepare_args(::Tuple{Any},::Tuple)@408",
      "prepare_args(::Tuple{},::Tuple)@409"],
    statement := "Preparing the real generated selector tuple produces one value for every original argument without dropping or duplicating a tuple position.",
    source := "base/broadcast.jl:350-358, 407-409; reconstructed argument cardinality invariant", status := .proven,
    prop := ``FlattenProofs.PreparedArgumentArity, thm := some ``FlattenProofs.preparedArgumentArity },
  { id := "broadcast-nested-single-leaf-evaluation", juliaFile := "base/broadcast.jl",
    juliaFns := ["_make_makeargs1(::Broadcasted,n)@400", "_make_makeargs1(_,n)@398",
      "Pick{N}(::Tuple)@395", "prepare_args(::Tuple{Any},::Tuple)@408"],
    statement := "A one-leaf nested evaluator calls its original function on the selected input value, preserving successful values and errors.",
    source := "base/broadcast.jl:350-357, 395-405; reconstruct nested argument evaluation", status := .proven,
    prop := ``FlattenProofs.NestedSingleLeafEvaluation, thm := some ``FlattenProofs.nestedSingleLeafEvaluation },
  { id := "broadcast-scalar-shape-identity", juliaFile := "base/broadcast.jl",
    juliaFns := ["_bcs(::Tuple{},::Tuple)@525", "_bcs(::Tuple,::Tuple{})@526"],
    statement := "Combining a scalar's empty shape with another shape preserves all entries of the non-scalar shape, in either argument order.",
    source := "base/broadcast.jl:506-518, 524-526; scalars do not add output dimensions", status := .proven,
    prop := ``ShapeIdentityProofs.ScalarShapeIdentity, thm := some ``ShapeIdentityProofs.scalarShapeIdentity },
  { id := "broadcast-style-identity-agreement", juliaFile := "base/broadcast.jl",
    juliaFns := ["result_style(::S,::S)@459", "result_join(::Any,::Any,::S,::S)@477"],
    statement := "Same-type style resolution succeeds exactly when the two style values are identical, and every successful result is that identical style.",
    source := "base/broadcast.jl:459-461, 477; inconsistent styles require a custom rule", status := .proven,
    prop := ``StyleProofs.IdentityAgreement, thm := some ``StyleProofs.identityAgreement },
  { id := "broadcast-validation-aligned-axes", juliaFile := "base/broadcast.jl",
    juliaFns := ["check_broadcast_axes(shp,A)@561", "check_broadcast_shape(shp,::Tuple)@557",
      "check_broadcast_shape(::Tuple{},::Tuple)@551", "_bcsm@536"],
    statement := "Shape validation succeeds exactly when every aligned source axis equals the destination dimension or has singleton length, and every source axis beyond the destination rank has singleton length.",
    source := "base/broadcast.jl:536, 551-561; complete singleton-expansion compatibility rule", status := .proven,
    prop := ``ValidationProofs.ValidationAlignedAxes, thm := some ``ValidationProofs.validationAlignedAxes },
  { id := "broadcast-validation-varying-axes", juliaFile := "base/broadcast.jl",
    juliaFns := ["check_broadcast_axes(shp,A)@561", "check_broadcast_shape(::Tuple{},::Tuple)@551",
      "check_broadcast_shape(shp,::Tuple)@557", "_bcsm@536"],
    statement := "A successful shape check cannot omit a non-singleton source axis beyond the destination rank.",
    source := "base/broadcast.jl:551-560; cannot broadcast an array to fewer non-singleton dimensions", status := .proven,
    prop := ``ValidationProofs.ValidationPreservesVaryingAxes, thm := some ``ValidationProofs.validationPreservesVaryingAxes },
  { id := "broadcast-instantiate-varying-axes", juliaFile := "base/broadcast.jl",
    juliaFns := ["instantiate(::Broadcasted)@310", "Broadcasted@176", "combine_axes(A)@504",
      "check_broadcast_axes(shp,A)@561", "check_broadcast_shape(::Tuple{},::Tuple)@551",
      "check_broadcast_shape(shp,::Tuple)@557"],
    statement := "Successful instantiation installs an axes tuple and cannot discard a varying dimension of its argument.",
    source := "base/broadcast.jl:310-318, 551-561; singleton-expansion and output-axes invariants", status := .proven,
    prop := ``ValidationProofs.InstantiationPreservesVaryingAxes, thm := some ``ValidationProofs.instantiationPreservesVaryingAxes },
  { id := "broadcast-tuple-instantiate-varying-axes", juliaFile := "base/broadcast.jl",
    juliaFns := ["instantiate(::Broadcasted{Style{Tuple}})@322", "check_broadcast_axes(shp,A)@561",
      "check_broadcast_shape(::Tuple{},::Tuple)@551", "check_broadcast_shape(shp,::Tuple)@557"],
    statement := "Successful tuple-style instantiation cannot omit any non-singleton source axis.",
    source := "base/broadcast.jl:322-325, 551-561; tuple-style shape validation", status := .proven,
    prop := ``ValidationProofs.TupleInstantiationPreservesVaryingAxes, thm := some ``ValidationProofs.tupleInstantiationPreservesVaryingAxes },
  { id := "broadcast-allocated-rank-axes", juliaFile := "base/broadcast.jl",
    juliaFns := ["similar(::Broadcasted{DefaultArrayStyle}, ::Type, dims)@230",
      "similar(::Broadcasted{ArrayConflict}, ::Type, dims)@235"],
    statement := "Default-array and conflict-style allocation derive the output rank from the supplied axes; every successful result's rank agrees with its stored axes.",
    source := "base/broadcast.jl:229-238; similar preserves the requested shape and array rank", status := .proven,
    prop := ``WrapperProofs.AllocatedRankMatchesAxes, thm := some ``WrapperProofs.allocatedRankMatchesAxes },
  { id := "broadcast-inferred-rank-least", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.ndims(::Type{<:Broadcasted{Any,Nothing}})@269", "argtype@252",
      "_maxndims(::Type{Tuple{}})@273", "_maxndims(::Type{Tuple{T}})@274", "_maxndims@275"],
    statement := "Inferred broadcast rank is at most a bound exactly when every argument rank is at most that bound; tuples contribute one dimension and empty argument lists contribute zero.",
    source := "base/broadcast.jl:269, 273-279; broadcast output dimensionality invariant", status := .proven,
    prop := ``RankProofs.InferredRankLeast, thm := some ``RankProofs.inferredRankLeast },
  { id := "broadcast-unfixed-style-rank-least", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.ndims(::Type{<:Broadcasted{<:AbstractArrayStyle,Nothing}})@270",
      "argtype@252", "_maxndims(::Type{Tuple{}})@273", "_maxndims(::Type{Tuple{T}})@274", "_maxndims@275"],
    statement := "A style without a fixed dimensionality infers the least rank that is at least every argument rank.",
    source := "base/broadcast.jl:270-279; AbstractArrayStyle{Any} supports arbitrary dimensionalities", status := .proven,
    prop := ``RankProofs.UnfixedStyleRankLeast, thm := some ``RankProofs.unfixedStyleRankLeast },
  { id := "broadcast-inferred-rank-permutation", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.ndims(::Type{<:Broadcasted{Any,Nothing}})@269",
      "_maxndims(::Type{Tuple{}})@273", "_maxndims(::Type{Tuple{T}})@274", "_maxndims@275"],
    statement := "Permuting the arguments preserves the inferred result rank.",
    source := "base/broadcast.jl:269, 273-279; broadcast dimensionality is independent of argument order", status := .proven,
    prop := ``RankProofs.RankPermutationInvariant, thm := some ``RankProofs.rankPermutationInvariant },
  { id := "broadcast-size-stored-rank", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.size(::Broadcasted)@281", "Base.axes(::Broadcasted)@240", "_axes(::Broadcasted, ::Tuple)@241"],
    statement := "An explicit output-axes tuple gives exactly one size component per dimension, even if the argument axes query fails or has a different rank.",
    source := "base/broadcast.jl:172, 240-243, 281; output axes may exceed those implied by the arguments", status := .proven,
    prop := ``WrapperProofs.StoredAxesRank, thm := some ``WrapperProofs.storedAxesRank },
  { id := "broadcast-size-nonnegative", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.size(::Broadcasted)@281", "Base.axes(::Broadcasted)@240",
      "_axes(::Broadcasted, ::Nothing)@242", "combine_axes(A)@504"],
    statement := "Every successful size query has nonnegative extents when its axes have valid nonnegative lengths.",
    source := "base/broadcast.jl:240-242, 281; size and axis-length invariant", status := .proven,
    prop := ``WrapperProofs.SizeExtentsNonnegative, thm := some ``WrapperProofs.sizeExtentsNonnegative },
  { id := "broadcast-axes-beyond-rank", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.axes(::Broadcasted, ::Integer)@245"],
    statement := "Every dimension greater than the declared broadcast rank has a singleton axis, independent of any stored axes or axes-query error.",
    source := "base/broadcast.jl:245-246; axes(A,d) has a singleton axis beyond ndims(A)", status := .proven,
    prop := ``WrapperProofs.BeyondRankSingleton, thm := some ``WrapperProofs.beyondRankSingleton },
  { id := "broadcast-wrapper-display", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.show(::IO, ::Broadcasted)@218"],
    statement := "Broadcasted display preserves the prior output, prints balanced wrapper punctuation, and includes style braces exactly for instantiated axes; its added length matches the rendered fields and punctuation.",
    source := "base/broadcast.jl:218-226; documented comment on suppressing intermediate broadcast styles", status := .proven,
    prop := ``WrapperProofs.DisplayPresentation, thm := some ``WrapperProofs.displayPresentation },
  { id := "broadcast-bottom-type-diagnostic", juliaFile := "base/broadcast.jl",
    juliaFns := ["BroadcastStyle(::Type{Union{}}, slurp...)@38"],
    statement := "The ambiguity MethodError identifies BroadcastStyle and preserves the count and position of every supplied argument after Union{}.",
    source := "base/broadcast.jl:38; MethodError argument-tuple invariant", status := .proven,
    prop := ``StyleProofs.BottomTypeDiagnostic, thm := some ``StyleProofs.bottomTypeDiagnostic },
  { id := "broadcast-style-dimension-join", juliaFile := "base/broadcast.jl",
    juliaFns := ["BroadcastStyle(::AbstractArrayStyle{M}, ::AbstractArrayStyle{N})@140",
      "BroadcastStyle(::AbstractArrayStyle{M}, ::DefaultArrayStyle{N})@149", "DefaultArrayStyle{M}(::Val{N})@99"],
    statement := "The real DefaultArrayStyle constructor makes each dimension join exactly an input rank that is at least both input ranks.",
    source := "base/broadcast.jl:51-77, 140-150; AbstractArrayStyle dimensionality invariant", status := .proven,
    prop := ``StyleProofs.DimensionJoin, thm := some ``StyleProofs.dimensionJoin },
  { id := "broadcast-style-dimension-associative", juliaFile := "base/broadcast.jl",
    juliaFns := ["BroadcastStyle(::AbstractArrayStyle{M}, ::DefaultArrayStyle{N})@149", "DefaultArrayStyle{M}(::Val{N})@99"],
    statement := "Combining three default-array ranks is independent of grouping, and combining two ranks is independent of argument order.",
    source := "base/broadcast.jl:51-77, 149-150; broadcast rank is independent of expression grouping", status := .proven,
    prop := ``StyleProofs.DimensionJoinAssociative, thm := some ``StyleProofs.dimensionJoinAssociative },
  { id := "broadcast-style-dimension-errors", juliaFile := "base/broadcast.jl",
    juliaFns := ["BroadcastStyle(::AbstractArrayStyle{M}, ::AbstractArrayStyle{N})@140",
      "BroadcastStyle(::AbstractArrayStyle{M}, ::DefaultArrayStyle{N})@149", "DefaultArrayStyle{M}(::Val{N})@99"],
    statement := "A failure in the external dimension comparison remains the same failure through either array-style join; broadcasting cannot replace it with a successful Any rank.",
    source := "base/broadcast.jl:140-150; propagation of the documented max comparison", status := .proven,
    prop := ``StyleProofs.DimensionJoinFailures, thm := some ``StyleProofs.dimensionJoinFailures },
  { id := "ranges-broadcast-add-length", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(+, ::AbstractUnitRange, ::Integer)@1188"],
    statement := "r .+ x on an integer unit range has the same length as r (as the elementwise broadcast does).",
    source := "base/broadcast.jl:783 broadcast docstring: broadcast applies f elementwise", status := .refuted,
    prop := ``IntegerProofs.BroadcastAddLengthPreserved, thm := some ``IntegerProofs.broadcastAddLength_refuted ,
    issue := "Existing refutation retained; see bugs/ranges-broadcast-add-length.yaml" },
  { id := "ranges-broadcast-mul-elementwise", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(*, ::AbstractRange, ::Number)@1222"],
    statement := "(r .* x)[i] equals r[i] * x for every valid index i of an integer range.",
    source := "base/broadcast.jl:783 broadcast docstring: broadcast applies f elementwise", status := .refuted,
    prop := ``IntegerProofs.BroadcastMulElementwise, thm := some ``IntegerProofs.broadcastMulElementwise_refuted ,
    issue := "Existing refutation retained; see bugs/ranges-broadcast-mul-elementwise.yaml" },
  { id := "floatranges-scalar-mul-broadcast", juliaFile := "base/broadcast.jl",
    juliaFns := ["*(::Real, ::StepRangeLen{<:Real,<:TwicePrecision})", "broadcasted(*, ::Number, ::StepRangeLen)@1216"],
    statement := "x * r and x .* r have identical elements for a Float64 range r.",
    source := "base/arraymath.jl:54 (*(::Number, ::AbstractArray) is broadcasting)", status := .refuted,
    prop := ``FloatProofs.ScalarMulBroadcast, thm := some ``FloatProofs.scalarMulBroadcast_refuted ,
    issue := "Existing refutation retained; see bugs/floatranges-scalar-mul-broadcast.yaml" },
  { id := "broadcastviews-shape-combination", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcast_shape(::Tuple,::Tuple,::Tuple...)@522", "_bcs(::Tuple,::Tuple)@527", "_bcs1(::Integer,::Integer)@531"],
    statement := "broadcast_shape on Int size tuples returns as many dimensions as the longest tuple; in each dimension every input extent is 1 or the result extent, which is one of the inputs. It throws only DimensionMismatch, and only when two extents of one dimension differ and neither is 1.",
    source := "base/broadcast.jl:506-518 (broadcast_shape docstring); manual doc/src/manual/arrays.md:1133-1135 (broadcast expands singleton dimensions)", status := .proven,
    prop := ``SizesProofs.ShapeCombination, thm := some ``SizesProofs.shapeCombination },
  { id := "broadcastviews-repeated-index-alias", juliaFile := "base/broadcast.jl",
    juliaFns := ["Base.Broadcast.broadcast_unalias", "Base.Broadcast.preprocess", "copyto!(::AbstractArray, ::Broadcasted{Nothing})"],
    statement := "dest .= dest .+ c for a view dest equals computing dest .+ c into a fresh array first, as P[I...] .+= c does.",
    source := "base/broadcast.jl:995-1001 (comment: the indices on the LHS and RHS will always match); base/views.jl:297-303 (@views docstring)", status := .refuted,
    prop := ``AliasProofs.SelfAssignFresh, thm := some ``AliasProofs.selfAssignFresh_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastviews-repeated-index-alias.yaml" },
  { id := "broadcastviews-range-singleton", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(+), ::AbstractRange, ::AbstractRange)@1198", "+(::OrdinalRange, ::OrdinalRange)"],
    statement := "r1 .+ r2 for two UnitRange{Int}s equals collect(r1) .+ collect(r2): a length-1 range is expanded and only unequal non-singleton lengths throw DimensionMismatch.",
    source := "manual doc/src/manual/arrays.md:1133-1135 (broadcast expands singleton dimensions); base/broadcast.jl:531", status := .refuted,
    prop := ``RangeProofs.RangeBroadcastPair, thm := some ``RangeProofs.rangeBroadcastPair_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastviews-range-singleton.yaml" },
  { id := "broadcastviews-range-ldiv", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(\\), ::Number, ::StepRangeLen)"],
    statement := "x .\\ r returns a range for every floating-point colon range r = a:s:b.",
    source := "invariant (x .\\ r computes x \\ r[i]); base/operators.jl:683-685 (\\ docstring)", status := .refuted,
    prop := ``RangeProofs.RangeLdivTotal, thm := some ``RangeProofs.rangeLdivTotal_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastviews-range-ldiv.yaml" },
  { id := "broadcastviews-range-unsigned-float", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(-), ::AbstractRange, ::Number)", "Base.floatrange", "unsafe_getindex(::StepRangeLen, ::Integer)"],
    statement := "r .- x for an unsigned StepRange{UInt64,UInt64} r and an integral x::Float64 has the elements r[i] - x of collect(r) .- x (small values, exact Float64 arithmetic).",
    source := "invariant (range broadcast methods, base/broadcast.jl:1174-1242, are optimizations of elementwise broadcast)", status := .refuted,
    prop := ``RangeProofs.RangeUnsignedFloat, thm := some ``RangeProofs.rangeUnsignedFloat_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastviews-range-unsigned-float.yaml" },
  { id := "broadcastviews-range-negate-unsigned", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(-), ::OrdinalRange)@1179"],
    statement := ".-r for r::UnitRange{UInt8} has the elements of .-collect(r).",
    source := "invariant (range broadcast methods, base/broadcast.jl:1174-1242, are optimizations of elementwise broadcast)", status := .refuted,
    prop := ``RangeProofs.RangeNegUnsigned, thm := some ``RangeProofs.rangeNegUnsigned_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastviews-range-negate-unsigned.yaml" },
  { id := "broadcastviews-shape-mixed-singleton", juliaFile := "base/broadcast.jl",
    juliaFns := ["_bcs1(::Integer,axis)@532", "_bcs1(axis,::Integer)@533"],
    statement := "_bcs1 on an Int size and a one-based axis (either order) throws exactly when both lengths differ from 1 and from each other, and otherwise returns an entry of the non-singleton length.",
    source := "base/broadcast.jl:506-518 (broadcast_shape docstring), 531 and 536 (singletons broadcast)", status := .refuted,
    prop := ``SizesProofs.ShapeMixedSingleton, thm := some ``SizesProofs.shapeMixedSingleton_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastviews-shape-mixed-singleton.yaml" },
  { id := "broadcastcov-linrange-shift-elementwise", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(+), ::LinRange, ::Number)@1196", "broadcasted(::DefaultArrayStyle{1}, ::typeof(-), ::LinRange, ::Number)@1210"],
    statement := "Broadcasting + or - between a Float64 LinRange and a scalar has the same Float64 elements as applying the operation to each original element.",
    source := "base/broadcast.jl:785-792 (broadcast applies the function over container elements)", status := .refuted,
    prop := ``FloatProofs.LinRangeShiftElementwise, thm := some ``FloatProofs.linRangeShiftElementwise_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastcov-linrange-shift-elementwise.yaml" },
  { id := "broadcastcov-steprangelen-div-elementwise", juliaFile := "base/broadcast.jl",
    juliaFns := ["broadcasted(::DefaultArrayStyle{1}, ::typeof(/), ::StepRangeLen, ::Number)@1231"],
    statement := "Broadcast division of a Float64 StepRangeLen by a scalar has the same Float64 elements as dividing each original element.",
    source := "base/broadcast.jl:785-792 (broadcast applies the function over container elements)", status := .refuted,
    prop := ``FloatProofs.StepRangeLenDivElementwise, thm := some ``FloatProofs.stepRangeLenDivElementwise_refuted ,
    issue := "Existing refutation retained; see bugs/broadcastcov-steprangelen-div-elementwise.yaml" },
  { id := "broadcast-shape-mismatch-exactly", juliaFile := "base/broadcast.jl", juliaFns := ["_bcs(::Tuple,::Tuple)@527", "_bcs1(::Integer,::Integer)@531"],
    statement := "For Int64 size tuples, DimensionMismatch occurs exactly when some dimension has conflicting non-singleton extents.",
    source := "broadcast docstring and indexing/storage invariants", status := .proven,
    prop := ``SizesProofs.ShapeMismatchExactly, thm := some ``SizesProofs.shapeMismatchExactly },
  { id := "broadcast-shape-order-independent", juliaFile := "base/broadcast.jl", juliaFns := ["_bcs(::Tuple,::Tuple)@527", "_bcs1(::Integer,::Integer)@531"],
    statement := "Combining Int64 size tuples is independent of argument order.",
    source := "broadcast docstring and indexing/storage invariants", status := .proven,
    prop := ``SizesProofs.ShapeCommutative, thm := some ``SizesProofs.shapeCommutative },
  { id := "broadcast-indexer-rank", juliaFile := "base/broadcast.jl", juliaFns := ["shapeindexer@607"],
    statement := "Precomputed keep flags and default indices have one entry per source dimension.",
    source := "broadcast docstring and indexing/storage invariants", status := .proven,
    prop := ``Elementwise.IndexerRank, thm := some ``Elementwise.indexerRank },
  { id := "broadcast-unexpanded-coordinates", juliaFile := "base/broadcast.jl", juliaFns := ["newindex(::CartesianIndex, keep, Idefault)@593"],
    statement := "Index remapping preserves all coordinates when no dimension is expanded.",
    source := "broadcast docstring and indexing/storage invariants", status := .proven,
    prop := ``Elementwise.UnexpandedCoordinates, thm := some ``Elementwise.unexpandedCoordinates },
  { id := "broadcast-scalar-result-rank", juliaFile := "base/broadcast.jl", juliaFns := ["_maxndims@275"],
    statement := "Every nonempty scalar argument tuple has zero-dimensional inferred broadcast output.",
    source := "broadcast docstring and indexing/storage invariants", status := .proven,
    prop := ``Elementwise.ScalarResultRank, thm := some ``Elementwise.scalarResultRank },
]
end JuliaLean.Proofs.base.broadcast
