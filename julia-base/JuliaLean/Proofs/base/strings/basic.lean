import JuliaLean.base.strings.basic
import JuliaLean.base.strings.substring
import JuliaLean.base.int
import JuliaLean.Proofs.base.int
import JuliaLean.base.operators
import JuliaLean.base.anyall
import JuliaLean.base.char
import JuliaLean.Registry.Types

/-!
# Properties of `base/strings/basic.jl`

Each registered statement is about the source-mirrored definitions in
`JuliaLean.base.strings.basic`. Callees defined in `base/strings/basic.jl`
(`ncodeunits`, `codeunit`, `thisind`, `prevind`, `nextind`, `lastindex`,
`firstindex`, `isempty`, `sizeof`, `length`, `getindex`, `checkbounds`,
`_isannotated`, `cmp`, `==`, `isless`, `isascii`, `_isascii`, `_isascii_chunks`,
`CodeUnits`, `codeunits`) are instantiated with their real definitions in
`JuliaLean.base.strings.basic`, and integer arithmetic, comparisons, and
conversions use `JuliaLean.base.int`, `JuliaLean.base.operators`, and `JuliaLean.base.anyall`.
-/

/-! Nothing to promise:
ncodeunits@68: required abstract-string interface declaration with no generic method body (also covered by `strings-basic-index-model`).
codeunit@82: required abstract-string interface declaration with no generic method body (also covered by `strings-basic-codeunits`).
eltype@161: trait method returning the default character element type `Char` (also covered by `strings-basic-index-model`).
first@183: forwards `first(s)` to `s[firstindex(s)]` (also covered by `stringscova-basic-getindex-faithful` and `strings-basic-index-model`).
getindex@190: colon indexing returns the string `s` unchanged (also covered by `stringscova-basic-getindex-faithful`).
string@218: single-argument constructor returning an `AbstractString` unchanged (also covered by `stringscova-basic-string-faithful`).
Vector{UInt8}@220: converts `s` to `String` and forwards to `unsafe_wrap(Vector{UInt8}, ...)`; byte-wrapping semantics belong to `String` and `unsafe_wrap`.
Array{UInt8}@221: converts `s` to `String` and forwards to `unsafe_wrap(Vector{UInt8}, ...)`; byte-wrapping semantics belong to `String` and `unsafe_wrap`.
Vector{T}@222: forwards character-vector construction to `collect(T, s)`.
Symbol@224: converts `s` to `String` and forwards to `Symbol(::String)`.
Symbol@225: formats heterogeneous arguments via `string(x...)` and forwards to `Symbol(::String)`.
convert@227: same-type string conversion returns `s` unchanged (also covered by `stringscova-basic-convert-faithful`).
convert@228: cross-type string conversion forwards to the target constructor `T(s)` (also covered by `stringscova-basic-convert-faithful`).
one@265: multiplicative string identity forwards to `convert(T, "")` (also covered by `stringscova-basic-convert-faithful` and `strings-basic-presentation`).
_isannotated@271: internal dispatch helper forwarding `typeof(s)` to `_isannotated(::Type)` (also covered by `strings-basic-presentation`).
length@396: single-argument `length(s)` forwards to `length(s, 1, ncodeunits(s))` (also covered by `strings-basic-length`).
length@410: converts generic `Integer` endpoints to `Int` and forwards to `length(s, ::Int, ::Int)` (also covered by `strings-basic-length`).
thisind@445: converts a generic `Integer` index to `Int` and forwards to `thisind(s, ::Int)` (also covered by `strings-basic-thisind-reverseind`).
prevind@501: converts generic `Integer` arguments to `Int` and forwards to `prevind(s, ::Int, ::Int)` (also covered by `strings-basic-prevind`).
prevind@502: converts a generic `Integer` index to `Int` and forwards to `prevind(s, ::Int)` (also covered by `strings-basic-prevind`).
prevind@503: two-argument `prevind(s, i::Int)` forwards to `prevind(s, i, 1)` (also covered by `strings-basic-prevind`).
nextind@560: converts generic `Integer` arguments to `Int` and forwards to `nextind(s, ::Int, ::Int)` (also covered by `strings-basic-nextind-first`).
nextind@561: converts a generic `Integer` index to `Int` and forwards to `nextind(s, ::Int, 1)` (also covered by `strings-basic-nextind-first`).
nextind@562: two-argument `nextind(s, i::Int)` forwards to `nextind(s, i, 1)` (also covered by `strings-basic-nextind-first`).
keys@580: wraps `s` in `EachStringIndex(s)` (also covered by `stringscova-basic-eachindex-faithful`).
length@582: forwards `length(e::EachStringIndex)` to `length(e.s)` (also covered by `stringscova-basic-eachindex-faithful`).
first@583: returns the starting index `1` for `EachStringIndex` (also covered by `stringscova-basic-eachindex-faithful`).
last@584: forwards `last(e::EachStringIndex)` to `lastindex(e.s)` (also covered by `stringscova-basic-eachindex-faithful`).
eltype@586: trait method returning `Int` for `EachStringIndex` (also covered by `stringscova-basic-eachindex-faithful`).
repeat@757: converts `s` to `String` and forwards to `repeat(::String, r)`.
^@772: forwards string and character exponentiation to `repeat(s, r)`.
CodeUnits@788: struct constructor storing the wrapped string `s` with codeunit type `codeunit(s)` (also covered by `strings-basic-codeunits`).
elsize@793: forwards `elsize(::Type{<:CodeUnits{T}})` to `sizeof(T)` (also covered by `strings-basic-codeunits`).
getindex@794: forwards `getindex(s::CodeUnits, i::Int)` to `codeunit(s.s, i)` (also covered by `strings-basic-codeunits`).
IndexStyle@795: trait constant returning `IndexLinear()` (also covered by `strings-basic-codeunits`).
checkbounds@796: forwards `checkbounds(Bool, s::CodeUnits, i)` to `checkbounds(Bool, s.s, i)` (also covered by `strings-basic-bounds-model` and `strings-basic-codeunits`).
dataids@798: forwards alias-detection storage identity to `dataids(s.s)`.
write@801: forwards `write(io, s::CodeUnits)` to `write(io, s.s)`.
cconvert@803: forwards `cconvert(::Type{Ptr{T}}, s::CodeUnits{T})` to `cconvert(Ptr{T}, s.s)`.
cconvert@804: forwards `cconvert(::Type{Ptr{Int8}}, s::CodeUnits{UInt8})` to `cconvert(Ptr{Int8}, s.s)`.
similar@806: forwards `similar(::Type{<:CodeUnits{T}}, dims)` to `similar(Array{T}, dims)`.
codeunits@827: forwards `codeunits(s)` to the `CodeUnits(s)` constructor (also covered by `strings-basic-codeunits`).
-/

namespace JuliaLean.Proofs.base.strings.basic

open _root_.JuliaLean _root_.JuliaLean.base.strings _root_.JuliaLean.base.strings.basic _root_.JuliaLean.Registry

abbrev Index := JuliaLean.base.strings.basic.Index

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error a, .error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun h' => h (Except.error.inj h'))
  | .ok a, .ok b =>
    if h : a = b then isTrue (congrArg Except.ok h)
    else isFalse (fun h' => h (Except.ok.inj h'))
  | .error _, .ok _ => isFalse nofun
  | .ok _, .error _ => isFalse nofun

@[simp] theorem throwThe_except {E α : Type} (e : E) :
    (throwThe E e : Except E α) = .error e := rfl

@[simp] theorem throw_except {E α : Type} (e : E) :
    (throw e : Except E α) = .error e := rfl

@[simp] theorem pure_except {E α : Type} (a : α) :
    (pure a : Except E α) = .ok a := rfl

@[simp] theorem bind_except_ok {E α β : Type} (a : α) (f : α → Except E β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem bind_except_error {E α β : Type} (e : E) (f : α → Except E β) :
    (Except.error e >>= f) = .error e := rfl

@[simp] theorem except_bind_ok {E α β : Type} (a : α) (f : α → Except E β) :
    Except.bind (Except.ok a) f = f a := rfl

@[simp] theorem except_bind_error {E α β : Type} (e : E) (f : α → Except E β) :
    Except.bind (Except.error e) f = .error e := rfl

@[simp] theorem except_map_ok {E α β : Type} (f : α → β) (a : α) :
    Except.map f (Except.ok a : Except E α) = .ok (f a) := rfl

@[simp] theorem except_map_error {E α β : Type} (f : α → β) (e : E) :
    Except.map f (Except.error e : Except E α) = .error e := rfl

def intMax : Index := basic.int ((2 : Int) ^ 63 - 1)
def intMin : Index := basic.int (-((2 : Int) ^ 63))
def accentString : StringData := ⟨[0xc3, 0xa9], [basic.int 1], [0xe9]⟩
def asciiString : StringData := ⟨[0x61], [basic.int 1], [0x61]⟩

/-! ## Arithmetic and conversion lemmas for `Index` (`JInt64`) -/

@[simp] theorem int_zero_val : (basic.int 0).val = 0 := by decide
@[simp] theorem int_one_val : (basic.int 1).val = 1 := by decide
@[simp] theorem int_two_val : (basic.int 2).val = 2 := by decide
@[simp] theorem int_neg_one_val : (basic.int (-1)).val = -1 := by decide

theorem index_bounds (z : Index) :
    -9223372036854775808 ≤ z.val ∧ z.val ≤ 9223372036854775807 :=
  z.property

theorem wrapInt_i64_of_bounds (x : Int)
    (h : -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807) :
    wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x h

theorem convert_i64_self (i : Index) : JuliaLean.base.int.convert .i64 i = .ok i := by
  simp [JuliaLean.base.int.convert, JInt.convert, i.property]

theorem convert_i64_of_inRange {t : IntTy} (x : JInt t)
    (h : IntTy.min .i64 ≤ x.val ∧ x.val ≤ IntTy.max .i64) :
    JuliaLean.base.int.convert .i64 x = .ok (basic.int x.val) := by
  unfold JuliaLean.base.int.convert JInt.convert
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  apply Subtype.ext
  exact (wrapInt_of_inRange .i64 x.val h).symm

theorem convert_i64_of_outOfRange {t : IntTy} (x : JInt t)
    (h : ¬ (IntTy.min .i64 ≤ x.val ∧ x.val ≤ IntTy.max .i64)) :
    JuliaLean.base.int.convert .i64 x = .error (.inexactError "Int64") := by
  simp [JuliaLean.base.int.convert, JInt.convert, h, IntTy.name]

theorem add_one_val (z : Index) (hmax : z.val + 1 ≤ IntTy.max .i64) :
    (z + basic.int 1).val = z.val + 1 := by
  have hz := index_bounds z
  have hmax' : z.val + 1 ≤ 9223372036854775807 := hmax
  change wrapInt .i64 (z.val + (basic.int 1).val) = z.val + 1
  rw [int_one_val]
  exact wrapInt_i64_of_bounds (z.val + 1) (by omega)

theorem sub_one_add_one (z : Index) (h0 : 0 ≤ z.val) :
    z - basic.int 1 + basic.int 1 = z := by
  have hz := index_bounds z
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 (z.val - (basic.int 1).val) + (basic.int 1).val) = z.val
  rw [int_one_val]
  have hsub : wrapInt .i64 (z.val - 1) = z.val - 1 :=
    wrapInt_i64_of_bounds (z.val - 1) (by omega)
  rw [hsub, show z.val - 1 + 1 = z.val by omega]
  exact wrapInt_i64_of_bounds z.val hz

theorem int_sub_eq_sub (a b : Index) : JuliaLean.base.int.sub a b = a - b := by
  apply Subtype.ext
  exact JuliaLean.Proofs.base.int.sub_int_val a b

theorem int_add_eq_add (a b : Index) : JuliaLean.base.int.add a b = a + b := by
  apply Subtype.ext
  exact JuliaLean.Proofs.base.int.add_int_val a b

theorem int_le_one_eq {t : IntTy} (i : JInt t) :
    JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1) i = decide (1 ≤ i.val) := by
  rw [JuliaLean.Proofs.base.int.le_eq]
  rfl

theorem int_le_ncodeunits_eq {t : IntTy} (i : JInt t) (n : Index) :
    JuliaLean.base.int.le i n = decide (i.val ≤ n.val) :=
  JuliaLean.Proofs.base.int.le_eq i n


theorem int_lt_eq {s t : IntTy} (x : JInt s) (y : JInt t) :
    JuliaLean.base.int.lt x y = decide (x.val < y.val) :=
  JuliaLean.Proofs.base.int.lt_eq x y

@[simp] theorem operators_max_index (a b : Index) :
    JuliaLean.base.operators.max
      (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
      JuliaLean.base.operators.ifelseValue a b =
    if b.val < a.val then a else b := by
  by_cases h : b.val < a.val <;>
    simp [JuliaLean.base.operators.max, JuliaLean.base.operators.islessReal,
      JuliaLean.base.operators.ifelseValue, int_lt_eq, h]

@[simp] theorem operators_min_index (a b : Index) :
    JuliaLean.base.operators.min
      (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
      JuliaLean.base.operators.ifelseValue a b =
    if b.val < a.val then b else a := by
  by_cases h : b.val < a.val <;>
    simp [JuliaLean.base.operators.min, JuliaLean.base.operators.islessReal,
      JuliaLean.base.operators.ifelseValue, int_lt_eq, h]

private theorem anyTupleLoop_bool {E α : Type} (p : α → Bool) :
    ∀ (xs : List α) (anymissing : Bool),
      JuliaLean.base.anyall.anyTupleLoop.loop
        (fun x => (.ok (.bool (p x)) : Except E JuliaLean.base.anyall.PredicateValue))
        anymissing xs =
      .ok (if xs.any p then some true else if anymissing then none else some false)
  | [], anymissing => by simp [JuliaLean.base.anyall.anyTupleLoop.loop]
  | x :: xs, anymissing => by
      unfold JuliaLean.base.anyall.anyTupleLoop.loop
      cases hx : p x
      · simpa [hx] using anyTupleLoop_bool p xs anymissing
      · simp [hx]

private theorem anyTupleStep_bool {E α : Type} (p : α → Bool) :
    ∀ (xs : List α) (anymissing : Bool),
      JuliaLean.base.anyall.anyTupleStep
        JuliaLean.base.anyall.anyTupleDone
        (fun x => (.ok (.bool (p x)) : Except E JuliaLean.base.anyall.PredicateValue))
        anymissing xs =
      .ok (if xs.any p then some true else if anymissing then none else some false)
  | [], anymissing => by simp [JuliaLean.base.anyall.anyTupleStep, JuliaLean.base.anyall.anyTupleDone]
  | x :: xs, anymissing => by
      unfold JuliaLean.base.anyall.anyTupleStep
      cases hx : p x
      · simpa [hx] using anyTupleStep_bool p xs anymissing
      · simp [hx]

@[simp] theorem anyTupleMethod_bool {E α : Type} (p : α → Bool)
    (isNTuple : Bool) (xs : List α) :
    JuliaLean.base.anyall.anyTupleMethod
      JuliaLean.base.anyall.anyTupleLoop
      JuliaLean.base.anyall.anyTupleStep
      JuliaLean.base.anyall.anyTupleDone
      (fun x => (.ok (.bool (p x)) : Except E JuliaLean.base.anyall.PredicateValue))
      isNTuple xs =
    .ok (some (xs.any p)) := by
  unfold JuliaLean.base.anyall.anyTupleMethod JuliaLean.base.anyall.anyTupleLoop
  split
  · rw [anyTupleLoop_bool p xs false]
    cases xs.any p <;> rfl
  · rw [anyTupleStep_bool p xs false]
    cases xs.any p <;> rfl

@[simp] theorem concat_eq {V1 V O E : Type}
    (annotatedString string : TypedValue V1 → List (TypedValue V) → Except E O)
    (s1 : TypedValue V1) (ss : List (TypedValue V)) (isNTuple : Bool) :
    basic.concat annotatedString string s1 ss isNTuple =
      if basic.isannotatedValue s1 || ss.any basic.isannotatedValue then
        annotatedString s1 ss
      else
        string s1 ss := by
  unfold basic.concat
  rw [anyTupleMethod_bool]

private theorem allAny_loop_bool {E α : Type} (p : α → Bool) :
    ∀ (xs : List α) (anymissing : Bool),
      JuliaLean.base.anyall.allAny.loop
        (fun x => (.ok (.bool (p x)) : Except E JuliaLean.base.anyall.PredicateValue))
        anymissing xs =
      .ok (if xs.all p then (if anymissing then none else some true) else some false)
  | [], anymissing => by simp [JuliaLean.base.anyall.allAny.loop]
  | x :: xs, anymissing => by
      unfold JuliaLean.base.anyall.allAny.loop
      cases hx : p x
      · simp [hx]
      · simpa [hx] using allAny_loop_bool p xs anymissing

theorem allPredicate_allAny_bool {E I α : Type} (items : I → List α) (p : α → Bool) (itr : I) :
    JuliaLean.base.anyall.allPredicate JuliaLean.base.anyall.allAny items
      (fun x => do pure (.bool (← (.ok (p x) : Except E Bool)))) itr =
    .ok (some ((items itr).all p)) := by
  unfold JuliaLean.base.anyall.allPredicate JuliaLean.base.anyall.allAny
  change JuliaLean.base.anyall.allAny.loop
    (fun x => (.ok (.bool (p x)) : Except E JuliaLean.base.anyall.PredicateValue))
    false (items itr) = .ok (some ((items itr).all p))
  rw [allAny_loop_bool p (items itr) false]
  cases (items itr).all p <;> rfl

private theorem allAny_loop_shortCircuit {E α : Type}
    (f : α → Except E Bool) :
    ∀ (before : List α) (decisive : α) (after : List α) (anymissing : Bool),
      (∀ x ∈ before, f x = .ok true) →
      f decisive = .ok false →
      JuliaLean.base.anyall.allAny.loop
        (fun x => do pure (.bool (← f x)))
        anymissing (before ++ decisive :: after) =
      .ok (some false)
  | [], decisive, after, anymissing, _, hdec => by
      simp [JuliaLean.base.anyall.allAny.loop, hdec]
  | x :: xs, decisive, after, anymissing, hbef, hdec => by
      have hx := hbef x (.head xs)
      have hxs : ∀ y ∈ xs, f y = .ok true := fun y hy => hbef y (.tail x hy)
      simpa [JuliaLean.base.anyall.allAny.loop, hx] using
        allAny_loop_shortCircuit f xs decisive after anymissing hxs hdec

private theorem allAny_loop_error {E α : Type}
    (f : α → Except E Bool) :
    ∀ (before : List α) (failing : α) (after : List α) (err : E) (anymissing : Bool),
      (∀ x ∈ before, f x = .ok true) →
      f failing = .error err →
      JuliaLean.base.anyall.allAny.loop
        (fun x => do pure (.bool (← f x)))
        anymissing (before ++ failing :: after) =
      .error (.predicate err)
  | [], failing, after, err, anymissing, _, hfail => by
      simp [JuliaLean.base.anyall.allAny.loop, hfail]
  | x :: xs, failing, after, err, anymissing, hbef, hfail => by
      have hx := hbef x (.head xs)
      have hxs : ∀ y ∈ xs, f y = .ok true := fun y hy => hbef y (.tail x hy)
      simpa [JuliaLean.base.anyall.allAny.loop, hx] using
        allAny_loop_error f xs failing after err anymissing hxs hfail
@[simp] theorem modelStringOps_ncodeunits {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).ncodeunits = ops.ncodeunits := rfl

@[simp] theorem modelStringOps_codeunit {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).codeunit = ops.codeunit := rfl

@[simp] theorem modelStringOps_codeunitType {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).codeunitType = ops.codeunitType := rfl

@[simp] theorem modelStringOps_codeunitSize {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).codeunitSize = ops.codeunitSize := rfl

@[simp] theorem modelStringOps_isvalid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).isvalid = ops.isvalid := rfl

@[simp] theorem modelStringOps_iterateAt {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).iterateAt = ops.iterateAt := rfl

@[simp] theorem modelStringOps_getindexSlice {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).getindexSlice = ops.getindexSlice := rfl

@[simp] theorem modelStringOps_boundsError {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).boundsError = ops.boundsError := rfl

@[simp] theorem modelStringOps_stringIndexError {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).stringIndexError = ops.stringIndexError := rfl

@[simp] theorem modelStringOps_argumentError {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).argumentError = ops.argumentError := rfl

@[simp] theorem modelStringOps_tupleTypeError {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).tupleTypeError = ops.tupleTypeError := rfl

@[simp] theorem modelStringOps_isBoundsError {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    (basic.modelStringOps ops intString).isBoundsError = ops.isBoundsError := rfl

@[simp] theorem modelStringOps_checkboundsBool {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i : Index) :
    (basic.modelStringOps ops intString).checkboundsBool s i =
      .ok (basic.checkboundsScalar ops.ncodeunits (fun i => decide (1 ≤ i.val))
        (fun i n => decide (i.val ≤ n.val)) s i) := rfl

@[simp] theorem modelStringOps_checkbounds {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i : Index) :
    (basic.modelStringOps ops intString).checkbounds s i =
      basic.checkbounds
        (fun s i => .ok (basic.checkboundsScalar ops.ncodeunits
          (fun i => decide (1 ≤ i.val)) (fun i n => decide (i.val ≤ n.val)) s i))
        ops.boundsError s i := rfl

@[simp] theorem modelStringOps_thisind {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i : Index) :
    (basic.modelStringOps ops intString).thisind s i = basic.thisindInt ops s i := rfl

@[simp] theorem modelStringOps_lastindex {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) :
    (basic.modelStringOps ops intString).lastindex s =
      basic.thisindInt ops s (ops.ncodeunits s) := rfl

@[simp] theorem modelStringOps_prevind {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i n : Index) :
    (basic.modelStringOps ops intString).prevind s i n =
      basic.previndInt { ops with thisind := basic.thisindInt ops } intString s i n := rfl

@[simp] theorem modelStringOps_nextind {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i n : Index) :
    (basic.modelStringOps ops intString).nextind s i n =
      basic.nextindInt { ops with thisind := basic.thisindInt ops } intString s i n := rfl

@[simp] theorem thisindLoop_modelStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) :
    ∀ (fuel : Nat) (i : Index),
      basic.thisindLoop (basic.modelStringOps ops intString) s fuel i =
        basic.thisindLoop ops s fuel i := by
  intro fuel
  induction fuel with
  | zero => intro i; rfl
  | succ fuel ih =>
      intro i
      unfold basic.thisindLoop
      simp [ih]

@[simp] theorem previndLoop_modelStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) :
    ∀ (fuel : Nat) (i n : Index),
      basic.previndLoop (basic.modelStringOps ops intString) s fuel i n =
        basic.previndLoop ops s fuel i n := by
  intro fuel
  induction fuel with
  | zero => intro i n; rfl
  | succ fuel ih =>
      intro i n
      unfold basic.previndLoop
      simp [ih]

@[simp] theorem previndLoop_thisindOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) :
    ∀ (fuel : Nat) (i n : Index),
      basic.previndLoop { ops with thisind := basic.thisindInt ops } s fuel i n =
        basic.previndLoop ops s fuel i n := by
  intro fuel
  induction fuel with
  | zero => intro i n; rfl
  | succ fuel ih =>
      intro i n
      unfold basic.previndLoop
      simp [ih]

@[simp] theorem nextindLoop_modelStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (z : Index) :
    ∀ (fuel : Nat) (i n : Index),
      basic.nextindLoop (basic.modelStringOps ops intString) s z fuel i n =
        basic.nextindLoop ops s z fuel i n := by
  intro fuel
  induction fuel with
  | zero => intro i n; rfl
  | succ fuel ih =>
      intro i n
      unfold basic.nextindLoop
      simp [ih]

@[simp] theorem nextindLoop_thisindOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) (z : Index) :
    ∀ (fuel : Nat) (i n : Index),
      basic.nextindLoop { ops with thisind := basic.thisindInt ops } s z fuel i n =
        basic.nextindLoop ops s z fuel i n := by
  intro fuel
  induction fuel with
  | zero => intro i n; rfl
  | succ fuel ih =>
      intro i n
      unfold basic.nextindLoop
      simp [ih]

@[simp] theorem lengthLoop_modelStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (last : Index) :
    ∀ (fuel : Nat) (k count : Index),
      basic.lengthLoop (basic.modelStringOps ops intString) s last fuel k count =
        basic.lengthLoop ops s last fuel k count := by
  intro fuel
  induction fuel with
  | zero => intro k count; rfl
  | succ fuel ih =>
      intro k count
      unfold basic.lengthLoop
      simp [ih]

theorem thisindInt_modelStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i : Index) :
    basic.thisindInt (basic.modelStringOps ops intString) s i = basic.thisindInt ops s i := by
  unfold basic.thisindInt
  simp only [modelStringOps_ncodeunits, modelStringOps_boundsError, thisindLoop_modelStringOps]
  rfl

theorem previndInt_modelStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i n : Index) :
    basic.previndInt (basic.modelStringOps ops intString) intString s i n =
      basic.previndInt { ops with thisind := basic.thisindInt ops } intString s i n := by
  unfold basic.previndInt
  simp only [modelStringOps_ncodeunits, modelStringOps_argumentError,
    modelStringOps_boundsError, modelStringOps_thisind, modelStringOps_stringIndexError,
    previndLoop_modelStringOps, previndLoop_thisindOps]
  rfl

theorem nextindInt_modelStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i n : Index) :
    basic.nextindInt (basic.modelStringOps ops intString) intString s i n =
      basic.nextindInt { ops with thisind := basic.thisindInt ops } intString s i n := by
  unfold basic.nextindInt
  simp only [modelStringOps_ncodeunits, modelStringOps_argumentError,
    modelStringOps_boundsError, modelStringOps_thisind, modelStringOps_stringIndexError,
    nextindLoop_modelStringOps, nextindLoop_thisindOps]
  rfl

/-! ## Helper lemmas for `IterSteps` and lexicographic comparison -/

def SameCharacters {C : Type} (equal : C → C → Bool) : List C → List C → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | c :: cs, d :: ds => equal c d && SameCharacters equal cs ds

def LexicallyLess {C : Type} (equal less : C → C → Bool) : List C → List C → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | c :: cs, d :: ds => if equal c d then LexicallyLess equal less cs ds else less c d

theorem sameCharacters_refl {C : Type} (equal : C → C → Bool)
    (hrefl : ∀ c, equal c c = true) :
    ∀ xs : List C, SameCharacters equal xs xs = true
  | [] => rfl
  | c :: cs => by simp [SameCharacters, hrefl c, sameCharacters_refl equal hrefl cs]

theorem lexCompare_zero_iff {C : Type} (equal less : C → C → Bool) (xs ys : List C) :
    (basic.lexCompare equal less xs ys).val = 0 ↔ SameCharacters equal xs ys = true := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [basic.lexCompare, SameCharacters, basic.int, JInt.lit,
        JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [basic.lexCompare, SameCharacters, basic.int, JInt.lit,
            JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]
      | cons y ys =>
          by_cases heq : equal x y
          · simp [basic.lexCompare, SameCharacters, heq, ih]
          · by_cases hless : less x y = true
            · simp [basic.lexCompare, SameCharacters, heq, hless, basic.int,
                JInt.lit, JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]
            · simp [basic.lexCompare, SameCharacters, heq, hless, basic.int,
                JInt.lit, JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]

theorem lexCompare_negative_iff {C : Type} (equal less : C → C → Bool) (xs ys : List C) :
    (basic.lexCompare equal less xs ys).val < 0 ↔ LexicallyLess equal less xs ys = true := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [basic.lexCompare, LexicallyLess, basic.int, JInt.lit,
        JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [basic.lexCompare, LexicallyLess, basic.int, JInt.lit,
            JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]
      | cons y ys =>
          by_cases heq : equal x y
          · simp [basic.lexCompare, LexicallyLess, heq, ih]
          · by_cases hless : less x y = true
            · simp [basic.lexCompare, LexicallyLess, heq, hless, basic.int,
                JInt.lit, JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]
            · simp [basic.lexCompare, LexicallyLess, heq, hless, basic.int,
                JInt.lit, JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed]

theorem lexCompare_dichotomy {C : Type} (equal less : C → C → Bool) (xs ys : List C) :
    basic.lexCompare equal less xs ys =
      if SameCharacters equal xs ys then basic.int 0
      else if LexicallyLess equal less xs ys then basic.int (-1)
      else basic.int 1 := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          by_cases heq : equal x y
          · simp [basic.lexCompare, SameCharacters, LexicallyLess, heq, ih]
          · by_cases hless : less x y = true <;>
              simp [basic.lexCompare, SameCharacters, LexicallyLess, heq, hless]

private theorem collectIterSteps_yield {A St E : Type}
    {x : A} {state : St} {next : St → IterSteps A St E} {xs : List A}
    (h : basic.collectIterSteps (.yield x state next) = .ok xs) :
    ∃ rest, basic.collectIterSteps (next state) = .ok rest ∧ xs = x :: rest := by
  cases hrest : basic.collectIterSteps (next state) with
  | error err =>
      simp [basic.collectIterSteps, hrest] at h
  | ok rest =>
      have h' : (Except.ok (x :: rest) : Except E (List A)) = .ok xs := by
        simpa [basic.collectIterSteps, hrest] using h
      exact ⟨rest, rfl, (Except.ok.inj h').symm⟩

private theorem collectIterSteps_ofList {A St E : Type} (st : St) :
    ∀ xs : List A, basic.collectIterSteps (E := E) (basic.iterStepsOfList st xs) = .ok xs
  | [] => rfl
  | x :: xs => by
      unfold basic.iterStepsOfList basic.collectIterSteps
      rw [collectIterSteps_ofList st xs]
      rfl

inductive IterateTrace {S C E : Type}
    (iterateAt : S → Index → Except E (Option (C × Index))) (s : S) :
    Option (C × Index) → List C → Prop where
  | none : IterateTrace iterateAt s none []
  | some {c : C} {i : Index} {next : Option (C × Index)} {rest : List C} :
      iterateAt s i = .ok next →
      IterateTrace iterateAt s next rest →
      IterateTrace iterateAt s (some (c, i)) (c :: rest)

def IteratesTo {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (chars : List C) : Prop :=
  ∃ first, ops.iterateFirst s = .ok first ∧
    IterateTrace ops.iterateAt s first chars ∧
    chars.length ≤ ops.iterationBound s

private theorem cmpLoop_lex {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) :
    ∀ {iv1 : Option (C × Index)} {charsA : List C},
      IterateTrace ops.iterateAt a iv1 charsA →
      ∀ {iv2 : Option (C × Index)} {charsB : List C} (fuel : Nat),
        IterateTrace ops.iterateAt b iv2 charsB →
        charsA.length + charsB.length < fuel →
        basic.cmpLoop ops a b fuel iv1 iv2 =
          .ok (basic.lexCompare ops.equalChar ops.lessChar charsA charsB) := by
  intro iv1 charsA hA
  induction hA with
  | none =>
      intro iv2 charsB fuel hB hfuel
      cases fuel with
      | zero => omega
      | succ f =>
          cases hB <;> rfl
  | @some c i nextA restA hnextA _ ih =>
      intro iv2 charsB fuel hB hfuel
      cases fuel with
      | zero => omega
      | succ f =>
          cases hB with
          | none => rfl
          | @some d j nextB restB hnextB htraceB =>
              unfold basic.cmpLoop
              by_cases heq : ops.equalChar c d = true
              · have hfuel' : restA.length + restB.length < f := by
                  simp at hfuel
                  omega
                simpa [heq, hnextA, hnextB, basic.lexCompare] using
                  ih f htraceB hfuel'
              · have hneq : ops.equalChar c d = false :=
                  Bool.eq_false_iff.mpr heq
                cases hless : ops.lessChar c d <;>
                  simp [hneq, hless, JuliaLean.base.operators.ifelseValue, basic.lexCompare]

private theorem cmp_of_iteratesTo {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) (charsA charsB : List C)
    (hsame : ops.sameReference a b = false)
    (hA : IteratesTo ops a charsA) (hB : IteratesTo ops b charsB) :
    basic.cmp ops a b =
      .ok (basic.lexCompare ops.equalChar ops.lessChar charsA charsB) := by
  rcases hA with ⟨iv1, hfirstA, htraceA, hboundA⟩
  rcases hB with ⟨iv2, hfirstB, htraceB, hboundB⟩
  have hloop := cmpLoop_lex ops a b htraceA
    (ops.iterationBound a + ops.iterationBound b + 1) htraceB (by omega)
  simpa [basic.cmp, hsame, hfirstA, hfirstB] using hloop
/-! ## Existing refutations -/

/-- `first(s,n)` returns the whole string once `n` covers its character count. -/
def FirstNAll : Prop :=
  ∀ (intString : Index → String) (s : StringData) (n : Index),
    Int.ofNat s.chars.length ≤ n.val →
      basic.firstN basic.stringDataOps (basic.nextindInt basic.stringDataOps intString)
        (JuliaLean.base.int.convert .i64) s n = .ok s

theorem firstNAll_refuted : ¬ FirstNAll := by
  intro h
  have hwhole := h (Function.const (α := String) (β := Index) "") accentString intMax (by decide)
  have hnext :
      basic.nextindInt basic.stringDataOps (Function.const (α := String) (β := Index) "") accentString
        (basic.int 0) intMax = .ok intMin := by
    decide
  have hconvert : JuliaLean.base.int.convert .i64 intMax = .ok intMax :=
    convert_i64_self intMax
  have hlast : basic.stringDataOps.lastindex accentString = .ok (basic.int 1) := by
    decide
  have hactual :
      basic.firstN basic.stringDataOps
        (basic.nextindInt basic.stringDataOps (Function.const (α := String) (β := Index) ""))
        (JuliaLean.base.int.convert .i64) accentString intMax =
        .ok StringData.empty := by
    unfold basic.firstN
    rw [hlast, hconvert]
    simp only [bind_except_ok, hnext]
    decide
  have hnot : StringData.empty ≠ accentString := by decide
  rw [hactual] at hwhole
  exact hnot (Except.ok.inj hwhole)

/-- `nextind(s,i,n)` with positive `n` advances past every in-bounds `i`. -/
def NextindNIncreasing : Prop :=
  ∀ (intString : Index → String) (s : StringData) (i n j : Index),
    0 ≤ i.val → i.val ≤ (basic.stringDataOps.ncodeunits s).val → 1 ≤ n.val →
    basic.nextindInt basic.stringDataOps intString s i n = .ok j → i.val < j.val

theorem nextindNIncreasing_refuted : ¬ NextindNIncreasing := by
  intro h
  have hactual :
      basic.nextindInt basic.stringDataOps (Function.const (α := String) (β := Index) "") asciiString
        (basic.int 1) intMax = .ok intMin := by
    decide
  have hstep := h (Function.const (α := String) (β := Index) "") asciiString (basic.int 1) intMax intMin
    (by decide) (by decide) (by decide) hactual
  exact (by decide : ¬ (basic.int 1).val < intMin.val) hstep

/-! ## Conversion, construction, and indexing -/

private theorem cmp_and_eq_of_same_iteratesTo {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (a b : S) (chars : List C)
    (hrefl : ∀ c, ops.equalChar c c = true)
    (hA : IteratesTo ops a chars) (hB : IteratesTo ops b chars) :
    basic.cmp ops a b = .ok (basic.int 0) ∧
    basic.eq ops a b = .ok true := by
  have hcmp : basic.cmp ops a b = .ok (basic.int 0) := by
    by_cases hsame : ops.sameReference a b = true
    · simp [basic.cmp, hsame]
    · have hsame' : ops.sameReference a b = false := Bool.eq_false_iff.mpr hsame
      have h := cmp_of_iteratesTo ops a b chars chars hsame' hA hB
      rw [lexCompare_dichotomy, sameCharacters_refl ops.equalChar hrefl chars] at h
      simpa using h
  exact ⟨hcmp, by simp [basic.eq, hcmp]⟩

def ConvertAllProperty : Prop :=
  (∀ (T E : Type) (construct : String → Except E T) (s : T),
    basic.oneString construct (.inl s) = basic.oneString construct (.inr ())) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (construct : String → Except E S)
      (annotatedString plainString : TypedValue S → List (TypedValue S) → Except E S)
      (s : TypedValue S) (t : AnnotType) (isNTuple : Bool) (e : S) (chars : List C),
    (∀ c, ops.equalChar c c = true) →
    construct "" = .ok e →
    IteratesTo ops e [] →
    IteratesTo ops s.val chars →
    (∀ (a b : TypedValue S) (ca cb : List C),
      IteratesTo ops a.val ca →
      IteratesTo ops b.val cb →
      (∃ ab, annotatedString a [b] = .ok ab ∧
        IteratesTo ops ab (ca ++ cb)) ∧
      (∃ ab, plainString a [b] = .ok ab ∧
        IteratesTo ops ab (ca ++ cb))) →
      (do
        let u ← basic.oneString construct (.inl s.val)
        let l ← basic.concat annotatedString plainString ⟨u, t⟩ [s] isNTuple
        basic.eq ops l s.val) = .ok true ∧
      (do
        let u ← basic.oneString construct (.inl s.val)
        let r ← basic.concat annotatedString plainString s [⟨u, t⟩] isNTuple
        basic.eq ops r s.val) = .ok true) ∧
  (∀ (s : TypedValue StringData) (t : AnnotType) (isNTuple : Bool),
    IteratesTo basic.stringDataOps s.val s.val.chars →
    ∃ e : StringData,
      basic.oneString (E := JlError) (fun str => .ok (basic.stringDataOfLeanString str))
        (.inl s.val) = .ok e ∧
      basic.ncodeunits basic.stringDataInterface e = basic.int 0 ∧
      basic.isemptyString basic.stringDataOps e = true ∧
      basic.sizeofString basic.stringDataOps e = basic.int 0 ∧
      basic.lengthString basic.stringDataOps (basic.lengthInt basic.stringDataOps) e =
        .ok (basic.int 0) ∧
      basic.cmp basic.stringDataOps e s.val =
        .ok (if s.val.chars.isEmpty then basic.int 0 else basic.int (-1)) ∧
      (do
        let l ← basic.concat basic.stringDataConcat basic.stringDataConcat ⟨e, t⟩ [s] isNTuple
        basic.eq basic.stringDataOps l s.val) = .ok true ∧
      (do
        let r ← basic.concat basic.stringDataConcat basic.stringDataConcat s [⟨e, t⟩] isNTuple
        basic.eq basic.stringDataOps r s.val) = .ok true) ∧
  (∀ (S T R C CU CT E : Type) (ops : StringOps T R C CU CT E)
      (construct : S → Except E T) (s : S) (t : T) (chars : List C),
    (∀ c, ops.equalChar c c = true) →
    construct s = .ok t →
    IteratesTo ops t chars →
      basic.cmp ops (basic.convertIdentity t) t = .ok (basic.int 0) ∧
      basic.eq ops (basic.convertIdentity t) t = .ok true ∧
      (do
        let out ← basic.convertString construct s
        basic.cmp ops out t) = .ok (basic.int 0) ∧
      (do
        let out ← basic.convertString construct s
        basic.eq ops out t) = .ok true) ∧
  (∀ (s : StringData) (chars : List UInt32),
    IteratesTo basic.stringDataOps s chars →
    let convId := basic.convertIdentity s
    basic.cmp basic.stringDataOps convId s = .ok (basic.int 0) ∧
    basic.eq basic.stringDataOps convId s = .ok true ∧
    basic.ncodeunits basic.stringDataInterface convId =
      basic.ncodeunits basic.stringDataInterface s ∧
    basic.codeunit basic.stringDataInterface convId = .uint8)

private theorem stringDataSpans_add_zero :
    ∀ (afterLast : Index) (starts : List Index) (chars : List UInt32),
      basic.stringDataSpans afterLast (starts.map (fun i => i + basic.int 0)) chars =
        basic.stringDataSpans afterLast starts chars
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | afterLast, first :: rest, c :: cs => by
      have hfirst : first + basic.int 0 = first := by
        apply Subtype.ext
        change wrapInt .i64 (first.val + 0) = first.val
        rw [Int.add_zero]
        exact wrapInt_of_inRange .i64 first.val first.property
      cases rest with
      | nil => simp [basic.stringDataSpans, hfirst]
      | cons next rs =>
          have hnext : next + basic.int 0 = next := by
            apply Subtype.ext
            change wrapInt .i64 (next.val + 0) = next.val
            rw [Int.add_zero]
            exact wrapInt_of_inRange .i64 next.val next.property
          simpa [basic.stringDataSpans, hfirst, hnext] using
            stringDataSpans_add_zero afterLast (next :: rs) cs

private theorem stringDataIterateAt_add_zero (s : StringData) (i : Index) :
    basic.stringDataIterateAt ⟨s.bytes, s.starts.map (fun j => j + basic.int 0), s.chars⟩ i =
      basic.stringDataIterateAt s i := by
  unfold basic.stringDataIterateAt
  dsimp only
  rw [stringDataSpans_add_zero]

private theorem iterateTrace_stringData_add_zero (s : StringData) :
    ∀ {iv : Option (UInt32 × Index)} {chars : List UInt32},
      IterateTrace basic.stringDataOps.iterateAt s iv chars →
      IterateTrace basic.stringDataOps.iterateAt
        ⟨s.bytes, s.starts.map (fun j => j + basic.int 0), s.chars⟩ iv chars := by
  intro iv chars h
  induction h with
  | none => exact .none
  | @some c i next rest hnext _ ih =>
      apply IterateTrace.some _ ih
      change Except.ok (basic.stringDataIterateAt
        ⟨s.bytes, s.starts.map (fun j => j + basic.int 0), s.chars⟩ i) = .ok next
      rw [stringDataIterateAt_add_zero s i]
      exact hnext

theorem convertAll_proven : ConvertAllProperty := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E ops construct annotatedString plainString s t isNTuple e chars
      hrefl he hce hcs hcat
    have hone : basic.oneString construct (.inl s.val) = .ok e := he
    rcases hcat ⟨e, t⟩ s [] chars hce hcs with ⟨⟨la, hla, hcla⟩, ⟨lp, hlp, hclp⟩⟩
    rcases hcat s ⟨e, t⟩ chars [] hcs hce with ⟨⟨ra, hra, hcra⟩, ⟨rp, hrp, hcrp⟩⟩
    rw [List.nil_append] at hcla hclp
    rw [List.append_nil] at hcra hcrp
    have heq_la := (cmp_and_eq_of_same_iteratesTo ops la s.val chars hrefl hcla hcs).2
    have heq_lp := (cmp_and_eq_of_same_iteratesTo ops lp s.val chars hrefl hclp hcs).2
    have heq_ra := (cmp_and_eq_of_same_iteratesTo ops ra s.val chars hrefl hcra hcs).2
    have heq_rp := (cmp_and_eq_of_same_iteratesTo ops rp s.val chars hrefl hcrp hcs).2
    constructor
    · rw [hone, bind_except_ok, concat_eq]
      split <;> simp [hla, hlp, heq_la, heq_lp]
    · rw [hone, bind_except_ok, concat_eq]
      split <;> simp [hra, hrp, heq_ra, heq_rp]
  · intro s t isNTuple hcs
    have hrefl : ∀ c : UInt32, basic.stringDataOps.equalChar c c = true := by
      intro c
      simp [basic.stringDataOps, basic.modelStringOps, basic.stringDataPrimOps]
    have he_iter : IteratesTo basic.stringDataOps StringData.empty [] :=
      ⟨none, rfl, .none, Nat.zero_le _⟩
    have heq_self := (cmp_and_eq_of_same_iteratesTo basic.stringDataOps
      s.val s.val s.val.chars hrefl hcs hcs).2
    refine ⟨StringData.empty, rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
    · have hcmp := cmp_of_iteratesTo basic.stringDataOps StringData.empty s.val
        [] s.val.chars rfl he_iter hcs
      rw [hcmp]
      cases s.val.chars <;> rfl
    · have hcatL : basic.concat basic.stringDataConcat basic.stringDataConcat
          ⟨StringData.empty, t⟩ [s] isNTuple = .ok ⟨s.val.bytes,
            s.val.starts.map (fun i => i + basic.int 0), s.val.chars⟩ := by
        rw [concat_eq]
        unfold basic.stringDataConcat
        split <;> rfl
      rw [hcatL, bind_except_ok]
      rcases hcs with ⟨iv1, hfirst, htrace, hbound⟩
      have hcs0 : IteratesTo basic.stringDataOps
          ⟨s.val.bytes, s.val.starts.map (fun i => i + basic.int 0), s.val.chars⟩
          s.val.chars := by
        refine ⟨iv1, ?_, iterateTrace_stringData_add_zero s.val htrace, hbound⟩
        change Except.ok (basic.stringDataIterateAt
          ⟨s.val.bytes, s.val.starts.map (fun i => i + basic.int 0), s.val.chars⟩ (basic.int 1)) =
          .ok iv1
        rw [stringDataIterateAt_add_zero s.val (basic.int 1)]
        exact hfirst
      exact (cmp_and_eq_of_same_iteratesTo basic.stringDataOps
        ⟨s.val.bytes, s.val.starts.map (fun i => i + basic.int 0), s.val.chars⟩ s.val
        s.val.chars hrefl hcs0 ⟨iv1, hfirst, htrace, hbound⟩).2
    · have hcatR : basic.concat basic.stringDataConcat basic.stringDataConcat
          s [⟨StringData.empty, t⟩] isNTuple = .ok s.val := by
        have h : basic.stringDataConcat s [⟨StringData.empty, t⟩] = .ok s.val := by
          unfold basic.stringDataConcat
          cases hs : s.val
          simp [StringData.empty]
        rw [concat_eq]
        split <;> exact h
      rw [hcatR, bind_except_ok]
      exact heq_self
  · intro S T R C CU CT E ops construct s t chars hrefl hconv hct
    have ⟨hcmp, heq⟩ := cmp_and_eq_of_same_iteratesTo ops t t chars hrefl hct hct
    refine ⟨hcmp, heq, ?_, ?_⟩ <;> simp [basic.convertString, hconv, hcmp, heq]
  · intro s chars hcs
    dsimp only
    have hrefl : ∀ c : UInt32, basic.stringDataOps.equalChar c c = true := by
      intro c
      simp [basic.stringDataOps, basic.modelStringOps, basic.stringDataPrimOps]
    have ⟨hcmp, heq⟩ := cmp_and_eq_of_same_iteratesTo basic.stringDataOps
      (basic.convertIdentity s) s chars hrefl hcs hcs
    exact ⟨hcmp, heq, rfl, rfl⟩

def StringProperty : Prop :=
  basic.stringEmpty = "" ∧
  basic.isemptyString basic.leanStringOps basic.stringEmpty = true ∧
  basic.sizeofString basic.leanStringOps basic.stringEmpty = basic.int 0 ∧
  basic.lengthString basic.leanStringOps (basic.lengthInt basic.leanStringOps) basic.stringEmpty =
    .ok (basic.int 0) ∧
  basic.lastindexString basic.leanStringOps basic.stringEmpty = .ok (basic.int 0) ∧
  basic.cmp basic.leanStringOps
    basic.stringEmpty (basic.stringIdentity basic.stringEmpty) = .ok (basic.int 0) ∧
  basic.eq basic.leanStringOps
    basic.stringEmpty (basic.stringIdentity basic.stringEmpty) = .ok true ∧
  (∀ (s : String) (c : _root_.Char) (cs : List _root_.Char),
    ("" == s) = false →
    s.toList = c :: cs →
      basic.cmp basic.leanStringOps
        basic.stringEmpty (basic.stringIdentity s) = .ok (basic.int (-1)) ∧
      basic.eq basic.leanStringOps
        basic.stringEmpty (basic.stringIdentity s) = .ok false ∧
      basic.isless basic.leanStringOps
        basic.stringEmpty (basic.stringIdentity s) = .ok true) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (chars : List C),
    (∀ c, ops.equalChar c c = true) →
    IteratesTo ops s chars →
      basic.stringIdentity s = s ∧
      basic.cmp ops (basic.stringIdentity s) s = .ok (basic.int 0) ∧
      basic.eq ops (basic.stringIdentity s) s = .ok true ∧
      basic.isemptyString ops (basic.stringIdentity s) = basic.isemptyString ops s ∧
      basic.sizeofString ops (basic.stringIdentity s) = basic.sizeofString ops s)

theorem string_proven : StringProperty := by
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro s c cs hne hs
    have hcmp : basic.cmp basic.leanStringOps
        basic.stringEmpty (basic.stringIdentity s) = .ok (basic.int (-1)) := by
      simp [basic.cmp, basic.stringEmpty, basic.stringIdentity, basic.leanStringOps,
        basic.modelStringOps, basic.leanStringPrimOps, hne, hs, basic.cmpLoop]
    refine ⟨hcmp, ?_, ?_⟩ <;> simp [basic.eq, basic.isless, hcmp]
  · intro S R C CU CT E ops s chars hrefl hchars
    have ⟨hcmp, heq⟩ := cmp_and_eq_of_same_iteratesTo ops s s chars hrefl hchars hchars
    exact ⟨rfl, hcmp, heq, rfl, rfl⟩

private theorem getindexVectorLoop_append_generic {S I St C E : Type}
    (checkbounds : S → I → Except E Unit)
    (isvalid : S → I → Except E Bool)
    (iterate : S → I → Except E (Option (C × Index)))
    (stringIndexError : S → I → E) (tupleTypeError : E)
    (s : S) (charAt : I → C) (nextAt : I → Index) :
    ∀ (steps : IterSteps I St E) (indices : List I) (acc : List C),
      basic.collectIterSteps steps = .ok indices →
      (∀ i ∈ indices,
        checkbounds s i = .ok () ∧
        isvalid s i = .ok true ∧
        iterate s i = .ok (some (charAt i, nextAt i))) →
      basic.getindexVectorLoop checkbounds isvalid iterate stringIndexError tupleTypeError
        (fun out c => .ok (out ++ [c])) s steps acc =
        .ok (acc ++ indices.map charAt) := by
  intro steps
  induction steps with
  | done =>
      intro indices acc hsteps _
      have hnil : indices = [] := by
        have h' : (Except.ok [] : Except E (List I)) = .ok indices := hsteps
        exact (Except.ok.inj h').symm
      subst indices
      simp [basic.getindexVectorLoop]
  | fail err =>
      intro _ _ hsteps _
      cases hsteps
  | yield i state next ih =>
      intro indices acc hsteps hall
      obtain ⟨rest, hrest, rfl⟩ := collectIterSteps_yield hsteps
      rcases hall i (.head rest) with ⟨hcb, hvalid, hiter⟩
      have hrest_all : ∀ j ∈ rest,
          checkbounds s j = .ok () ∧
          isvalid s j = .ok true ∧
          iterate s j = .ok (some (charAt j, nextAt j)) :=
        fun j hj => hall j (.tail i hj)
      simpa [basic.getindexVectorLoop, basic.getindexInteger,
        hcb, hvalid, hiter, List.map, List.append_assoc] using
        ih state rest (acc ++ [charAt i]) hrest hrest_all

def GetindexProperty : Prop :=
  (∀ (S C D E I : Type) (ncodeunits : S → Index) (toInt : I → Int)
      (isvalid : S → I → Except E Bool)
      (iterate : S → I → Except E (Option (C × Index)))
      (boundsError stringIndexError : S → I → E) (tupleTypeError : E)
      (s : S) (i : I) (default : D),
    let cbBool := fun s i =>
      (.ok (basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
        (fun i n => decide (toInt i ≤ n.val)) s i) : Except E Bool)
    let cb := basic.checkbounds cbBool boundsError
    let getidx := basic.getindexInteger cb isvalid iterate stringIndexError tupleTypeError
    (¬ (1 ≤ toInt i ∧ toInt i ≤ (ncodeunits s).val) →
      getidx s i = .error (boundsError s i) ∧
      basic.getString cbBool getidx s i default = .ok (.inr default)) ∧
    (1 ≤ toInt i ∧ toInt i ≤ (ncodeunits s).val →
      basic.getString cbBool getidx s i default = (getidx s i).map Sum.inl) ∧
    (1 ≤ toInt i ∧ toInt i ≤ (ncodeunits s).val →
      isvalid s i = .ok false →
      getidx s i = .error (stringIndexError s i)) ∧
    (∀ (c : C) (next : Index),
      1 ≤ toInt i ∧ toInt i ≤ (ncodeunits s).val →
      isvalid s i = .ok true →
      iterate s i = .ok (some (c, next)) →
      getidx s i = .ok c ∧
      basic.getString cbBool getidx s i default = .ok (.inl c))) ∧
  (∀ (t : IntTy) (S R C CU CT D E : Type) (ops : StringOps S R C CU CT E)
      (boundsErr strIdxErr : S → JInt t → E)
      (isvalid : S → JInt t → Except E Bool)
      (iterate : S → JInt t → Except E (Option (C × Index)))
      (s : S) (i : JInt t) (default : D),
    let cbBool := fun s (i : JInt t) =>
      (.ok (basic.checkboundsScalar ops.ncodeunits
        (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
        (fun i n => JuliaLean.base.int.le i n) s i) : Except E Bool)
    let cb := basic.checkbounds cbBool boundsErr
    let getidx := basic.getindexInteger cb isvalid iterate strIdxErr ops.tupleTypeError
    (¬ (1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val) →
      getidx s i = .error (boundsErr s i) ∧
      basic.getString cbBool getidx s i default = .ok (.inr default)) ∧
    (1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val →
      basic.getString cbBool getidx s i default = (getidx s i).map Sum.inl)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (next : Index) (c : C),
    1 ≤ (ops.ncodeunits s).val →
    ops.isvalid s (basic.int 1) = .ok true →
    ops.iterateAt s (basic.int 1) = .ok (some (c, next)) →
      basic.firstString (basic.getindexString (basic.modelStringOps ops intString)) s = .ok c) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (i : Index),
    basic.getindexColon s = s ∧
    basic.getindexString (basic.modelStringOps ops intString) (basic.getindexColon s) i =
      basic.getindexString (basic.modelStringOps ops intString) s i ∧
    basic.isemptyString ops (basic.getindexColon s) = basic.isemptyString ops s) ∧
  (∀ (S C V I St E : Type) (ncodeunits : S → Index) (toInt : I → Int)
      (isvalid : S → I → Except E Bool)
      (iterate : S → I → Except E (Option (C × Index)))
      (boundsError stringIndexError : S → I → E) (tupleTypeError : E)
      (lengthV : V → Except E Index)
      (iterateV : V → IterSteps I St E)
      (s : S) (v : V) (hint : Index) (indices : List I)
      (charAt : I → C) (nextAt : I → Index),
    let cbBool := fun s i =>
      (.ok (basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
        (fun i n => decide (toInt i ≤ n.val)) s i) : Except E Bool)
    let cb := basic.checkbounds cbBool boundsError
    lengthV v = .ok hint →
    basic.collectIterSteps (iterateV v) = .ok indices →
    (∀ i ∈ indices,
      1 ≤ toInt i ∧ toInt i ≤ (ncodeunits s).val ∧
      isvalid s i = .ok true ∧
      iterate s i = .ok (some (charAt i, nextAt i))) →
      basic.getindexVector cb isvalid iterate stringIndexError tupleTypeError
        lengthV iterateV (fun out c => .ok (out ++ [c]))
        (fun action _ => action []) s v = .ok (indices.map charAt)) ∧
  (∀ (S C V I St E : Type) (ncodeunits : S → Index) (toInt : I → Int)
      (isvalid : S → I → Except E Bool)
      (iterate : S → I → Except E (Option (C × Index)))
      (boundsError stringIndexError : S → I → E) (tupleTypeError : E)
      (lengthV : V → Except E Index)
      (iterateV : V → IterSteps I St E)
      (s : S) (v : V) (hint : Index) (i : I) (state : St) (next : St → IterSteps I St E),
    let cbBool := fun s i =>
      (.ok (basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
        (fun i n => decide (toInt i ≤ n.val)) s i) : Except E Bool)
    let cb := basic.checkbounds cbBool boundsError
    lengthV v = .ok hint →
    iterateV v = .yield i state next →
    ¬ (1 ≤ toInt i ∧ toInt i ≤ (ncodeunits s).val) →
      basic.getindexVector cb isvalid iterate stringIndexError tupleTypeError
        lengthV iterateV (fun out c => .ok (out ++ [c]))
        (fun action _ => action []) s v = .error (boundsError s i)) ∧
  (∀ (S R C CU CT V O E : Type) (ops : StringOps S R C CU CT E) (s : S) (v : V),
    basic.getindexBoolVector (O := O) ops s v =
      .error (ops.argumentError "logical indexing not supported for strings"))

theorem getindex_proven : GetindexProperty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · intro S C D E I ncodeunits toInt isvalid iterate boundsError stringIndexError tupleTypeError
      s i default
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hbound
      have hcb : basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
          (fun i n => decide (toInt i ≤ n.val)) s i = false := by
        simp only [basic.checkboundsScalar, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      exact ⟨by simp [basic.getindexInteger, basic.checkbounds, hcb],
        by simp [basic.getString, hcb]⟩
    · intro hbound
      have hcb : basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
          (fun i n => decide (toInt i ≤ n.val)) s i = true := by
        simp [basic.checkboundsScalar, hbound.1, hbound.2]
      cases hget : basic.getindexInteger
        (basic.checkbounds (fun s i => .ok (basic.checkboundsScalar ncodeunits
          (fun i => decide (1 ≤ toInt i)) (fun i n => decide (toInt i ≤ n.val)) s i))
          boundsError)
        isvalid iterate stringIndexError tupleTypeError s i <;>
        simp [basic.getString, hcb, hget]
    · intro hbound hinvalid
      have hcb : basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
          (fun i n => decide (toInt i ≤ n.val)) s i = true := by
        simp [basic.checkboundsScalar, hbound.1, hbound.2]
      simp [basic.getindexInteger, basic.checkbounds, hcb, hinvalid]
    · intro c next hbound hvalid hiter
      have hcb : basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
          (fun i n => decide (toInt i ≤ n.val)) s i = true := by
        simp [basic.checkboundsScalar, hbound.1, hbound.2]
      exact ⟨by simp [basic.getindexInteger, basic.checkbounds, hcb, hvalid, hiter],
        by simp [basic.getString, basic.getindexInteger, basic.checkbounds, hcb, hvalid, hiter]⟩
  · intro t S R C CU CT D E ops boundsErr strIdxErr isvalid iterate s i default
    dsimp only
    constructor
    · intro hbound
      have hcb : basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i = false := by
        simp only [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq,
          Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      exact ⟨by simp [basic.getindexInteger, basic.checkbounds, hcb],
        by simp [basic.getString, hcb]⟩
    · intro hbound
      have hcb : basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i = true := by
        simp [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq, hbound.1, hbound.2]
      cases hget : basic.getindexInteger
        (basic.checkbounds (fun s (i : JInt t) => .ok (basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i)) boundsErr)
        isvalid iterate strIdxErr ops.tupleTypeError s i <;>
        simp [basic.getString, hcb, hget]
  · intro S R C CU CT E ops intString s next c hlen hvalid hiter
    have hcb : basic.checkboundsScalar ops.ncodeunits (fun i => decide (1 ≤ i.val))
        (fun i n => decide (i.val ≤ n.val)) s (basic.int 1) = true := by
      simp [basic.checkboundsScalar, hlen]
    simp [basic.firstString, basic.firstindexString, basic.getindexString,
      basic.getindexInteger, basic.checkbounds, hcb, hvalid, hiter]
  · intro S R C CU CT E ops intString s i
    exact ⟨rfl, rfl, rfl⟩
  · intro S C V I St E ncodeunits toInt isvalid iterate boundsError stringIndexError
      tupleTypeError lengthV iterateV s v hint indices charAt nextAt _ _ hlen hsteps hall
    have hall' : ∀ i ∈ indices,
        basic.checkbounds
          (fun s i => .ok (basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
            (fun i n => decide (toInt i ≤ n.val)) s i))
          boundsError s i = .ok () ∧
        isvalid s i = .ok true ∧
        iterate s i = .ok (some (charAt i, nextAt i)) := by
      intro i hi
      rcases hall i hi with ⟨hlo, hhi, hval, hit⟩
      exact ⟨by simp [basic.checkbounds, basic.checkboundsScalar, hlo, hhi], hval, hit⟩
    simpa [basic.getindexVector, hlen] using
      getindexVectorLoop_append_generic
        (basic.checkbounds
          (fun s i => .ok (basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
            (fun i n => decide (toInt i ≤ n.val)) s i))
          boundsError)
        isvalid iterate stringIndexError tupleTypeError s charAt nextAt
        (iterateV v) indices [] hsteps hall'
  · intro S C V I St E ncodeunits toInt isvalid iterate boundsError stringIndexError
      tupleTypeError lengthV iterateV s v hint i state next cbBool cb hlen hiter hbound
    have hcb : basic.checkboundsScalar ncodeunits (fun i => decide (1 ≤ toInt i))
        (fun i n => decide (toInt i ≤ n.val)) s i = false := by
      simp only [basic.checkboundsScalar, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    simp [basic.getindexVector, hlen, hiter, basic.getindexVectorLoop,
      basic.getindexInteger, cb, cbBool, basic.checkbounds, hcb]

def StringIndexProperty : Prop :=
  (∀ (S : Type), basic.eltypeString S = basic.Char) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S),
    basic.firstindexString s = basic.int 1 ∧
    basic.firstString (basic.getindexString (basic.modelStringOps ops intString)) s =
      basic.getindexString (basic.modelStringOps ops intString) s (basic.int 1)) ∧
  (∀ (S E : Type) (iface : AbstractStringInterface S E) (s : S) (i : Index),
    basic.codeunit iface s ∈ basic.CodeunitType ∧
    ((1 ≤ i.val ∧ i.val ≤ (basic.ncodeunits iface s).val) ↔
      ∃ u : (basic.codeunit iface s).toType, iface.codeunitAt s i = .ok u) ∧
    (basic.checkboundsScalar (basic.ncodeunits iface)
      (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
      (fun i n => JuliaLean.base.int.le i n) s i = true ↔
      ∃ u : (basic.codeunit iface s).toType, iface.codeunitAt s i = .ok u) ∧
    (1 ≤ (basic.ncodeunits iface s).val ↔
      ∃ u : (basic.codeunit iface s).toType,
        iface.codeunitAt s (basic.firstindexString s) = .ok u)) ∧
  (∀ (s : StringData) (i : Index),
    basic.ncodeunits basic.stringDataInterface s = basic.int (s.bytes.length : Int) ∧
    basic.codeunit basic.stringDataInterface s = .uint8 ∧
    .uint8 ∈ basic.CodeunitType ∧
    (basic.codeunit basic.stringDataInterface s).toType = UInt8 ∧
    (basic.checkboundsScalar basic.stringDataOps.ncodeunits
      (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
      (fun i n => JuliaLean.base.int.le i n) s i = true ↔
      (1 ≤ i.val ∧ i.val ≤ (basic.stringDataOps.ncodeunits s).val)) ∧
    (1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int) →
      basic.stringDataOps.codeunit s i =
        .ok (s.bytes.getD (i.val.toNat - 1) 0 :
          (basic.codeunit basic.stringDataInterface s).toType)) ∧
    (¬ (1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int)) →
      basic.stringDataOps.codeunit s i = .error .boundsError) ∧
    (1 ≤ s.bytes.length →
      basic.stringDataOps.codeunit s (basic.int 1) =
        .ok (s.bytes.getD 0 0 :
          (basic.codeunit basic.stringDataInterface s).toType))) ∧
  (∀ (S R C CU CT E I : Type) (ops : StringOps S R C CU CT E)
      (isInt : I → Bool) (toInt : I → Except E Index) (s : S) (i : I),
    (isInt i = true →
      basic.codeunitInteger ops isInt toInt s i = .error (.methodError "codeunit" (s, i)) ∧
      basic.isvalidInteger ops isInt toInt s i = .error (.methodError "isvalid" (s, i)) ∧
      basic.iterateInteger ops isInt toInt s i = .error (.methodError "iterate" (s, i))) ∧
    (∀ idx : Index,
      isInt i = false → toInt i = .ok idx →
      basic.codeunitInteger ops isInt toInt s i =
        (ops.codeunit s idx).mapError MethodCallError.base ∧
      basic.isvalidInteger ops isInt toInt s i =
        (ops.isvalid s idx).mapError MethodCallError.base ∧
      basic.iterateInteger ops isInt toInt s i =
        (ops.iterateAt s idx).mapError MethodCallError.base) ∧
    (∀ err : E,
      isInt i = false → toInt i = .error err →
      basic.codeunitInteger ops isInt toInt s i = .error (.base err) ∧
      basic.isvalidInteger ops isInt toInt s i = .error (.base err) ∧
      basic.iterateInteger ops isInt toInt s i = .error (.base err))) ∧
  (∀ (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (s : S) (i : JInt .i64),
    basic.codeunitInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
      .error (.methodError "codeunit" (s, i)) ∧
    basic.isvalidInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
      .error (.methodError "isvalid" (s, i)) ∧
    basic.iterateInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
      .error (.methodError "iterate" (s, i))) ∧
  (∀ (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (t : IntTy) (s : S) (i : JInt t),
    t ≠ .i64 →
    IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 →
      basic.codeunitInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
        (ops.codeunit s (basic.int i.val)).mapError MethodCallError.base ∧
      basic.isvalidInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
        (ops.isvalid s (basic.int i.val)).mapError MethodCallError.base ∧
      basic.iterateInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
        (ops.iterateAt s (basic.int i.val)).mapError MethodCallError.base) ∧
  (∀ (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (t : IntTy) (s : S) (i : JInt t),
    t ≠ .i64 →
    ¬ (IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64) →
      basic.codeunitInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
        .error (.base (.inexactError "Int64")) ∧
      basic.isvalidInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
        .error (.base (.inexactError "Int64")) ∧
      basic.iterateInteger ops basic.isaInt (JuliaLean.base.int.convert .i64) s i =
        .error (.base (.inexactError "Int64"))) ∧
  (∀ (S R C CU E : Type) (iface : AbstractStringInterface S E)
      (ops : StringOps S R C CU CodeunitTag E) (s : S),
    ops.ncodeunits = basic.ncodeunits iface →
    ops.codeunitType = basic.codeunit iface →
    ops.codeunitSize = CodeunitTag.byteSize →
      (basic.isemptyString ops s = true ↔ basic.ncodeunits iface s = basic.int 0) ∧
      (0 ≤ (basic.ncodeunits iface s).val →
        (basic.isemptyString ops s = false ↔ 1 ≤ (basic.ncodeunits iface s).val)) ∧
      (basic.isemptyString ops s = true → basic.sizeofString ops s = basic.int 0) ∧
      (0 ≤ (basic.ncodeunits iface s).val →
        4 * (basic.ncodeunits iface s).val ≤ IntTy.max .i64 →
        (basic.sizeofString ops s).val =
          (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val ∧
        (1 ≤ (basic.ncodeunits iface s).val →
          1 ≤ (basic.sizeofString ops s).val ∧
          (basic.ncodeunits iface s).val ≤ (basic.sizeofString ops s).val)))

theorem stringIndex_proven : StringIndexProperty := by
  refine ⟨fun _ => rfl, fun _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S E iface s i
    refine ⟨iface.codeunit_mem s, iface.codeunitAt_inbounds s i, ?_, ?_⟩
    · dsimp [basic.checkboundsScalar, basic.ncodeunits]
      rw [int_le_one_eq, int_le_ncodeunits_eq, Bool.and_eq_true,
        decide_eq_true_eq, decide_eq_true_eq]
      exact iface.codeunitAt_inbounds s i
    · have h1 := iface.codeunitAt_inbounds s (basic.firstindexString s)
      have hfirst : (basic.firstindexString s).val = 1 := rfl
      rw [hfirst] at h1
      exact ⟨fun h => h1.mp ⟨Int.le_refl 1, h⟩, fun h => (h1.mpr h).2⟩
  · intro s i
    refine ⟨rfl, rfl, by decide, rfl, ?_, ?_, ?_, ?_⟩
    · dsimp [basic.checkboundsScalar]
      rw [int_le_one_eq, int_le_ncodeunits_eq]
      simp
    · rintro ⟨h1, h2⟩
      have hcond : (decide (1 ≤ i.val) && decide (i.val ≤ (s.bytes.length : Int))) = true := by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨h1, h2⟩
      change (if (decide (1 ≤ i.val) && decide (i.val ≤ (s.bytes.length : Int))) = true then _ else _) = _
      rw [hcond]
      rfl
    · intro hout
      have hcond : (decide (1 ≤ i.val) && decide (i.val ≤ (s.bytes.length : Int))) = false := by
        rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
        omega
      change (if (decide (1 ≤ i.val) && decide (i.val ≤ (s.bytes.length : Int))) = true then _ else _) = _
      rw [hcond]
      rfl
    · intro h1
      have hcond : (decide ((1 : Int) ≤ 1) && decide ((1 : Int) ≤ (s.bytes.length : Int))) = true := by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        omega
      change (if (decide ((1 : Int) ≤ 1) && decide ((1 : Int) ≤ (s.bytes.length : Int))) = true then _ else _) = _
      rw [hcond]
      rfl
  · intro S R C CU CT E I ops isInt toInt s i
    refine ⟨?_, ?_, ?_⟩
    · intro hisa
      simp [basic.codeunitInteger, basic.isvalidInteger, basic.iterateInteger, hisa]
    · intro idx hisa hto
      refine ⟨?_, ?_, ?_⟩
      · cases hcu : ops.codeunit s idx <;>
          simp [basic.codeunitInteger, hisa, hto, hcu, Except.mapError]
      · cases hval : ops.isvalid s idx <;>
          simp [basic.isvalidInteger, hisa, hto, hval, Except.mapError]
      · cases hit : ops.iterateAt s idx <;>
          simp [basic.iterateInteger, hisa, hto, hit, Except.mapError]
    · intro err hisa hto
      simp [basic.codeunitInteger, basic.isvalidInteger, basic.iterateInteger, hisa, hto]
  · intro S R C CU CT ops s i
    exact ⟨rfl, rfl, rfl⟩
  · intro S R C CU CT ops t s i hne hin
    have hisa : basic.isaInt i = false := by
      simp [basic.isaInt, beq_eq_false_iff_ne, hne]
    have hconv := convert_i64_of_inRange i hin
    refine ⟨?_, ?_, ?_⟩
    · cases hcu : ops.codeunit s (basic.int i.val) <;>
        simp [basic.codeunitInteger, hisa, hconv, hcu, Except.mapError]
    · cases hval : ops.isvalid s (basic.int i.val) <;>
        simp [basic.isvalidInteger, hisa, hconv, hval, Except.mapError]
    · cases hit : ops.iterateAt s (basic.int i.val) <;>
        simp [basic.iterateInteger, hisa, hconv, hit, Except.mapError]
  · intro S R C CU CT ops t s i hne hout
    have hisa : basic.isaInt i = false := by
      simp [basic.isaInt, beq_eq_false_iff_ne, hne]
    have hconv := convert_i64_of_outOfRange i hout
    simp [basic.codeunitInteger, basic.isvalidInteger, basic.iterateInteger, hisa, hconv]
  · intro S R C CU E iface ops s hnc hct hcs
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [basic.isemptyString, hnc, beq_iff_eq]
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
    · intro h0
      simp only [basic.isemptyString, hnc, beq_eq_false_iff_ne]
      omega
    · intro hempty
      have hzero : ops.ncodeunits s = basic.int 0 := by
        apply Subtype.ext
        simpa [basic.isemptyString] using hempty
      rw [basic.sizeofString, hzero]
      apply Subtype.ext
      change wrapInt .i64 (0 * (ops.codeunitSize (ops.codeunitType s)).val) = 0
      simp [wrapInt_of_inRange .i64 0 (by decide)]
    · intro h0 hmax4
      have hmax4' : 4 * (basic.ncodeunits iface s).val ≤ 9223372036854775807 := hmax4
      have hsz : 1 ≤ ((basic.codeunit iface s).byteSize).val ∧
          ((basic.codeunit iface s).byteSize).val ≤ 4 := by
        cases basic.codeunit iface s <;> decide
      have hprod_le : (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val ≤
          4 * (basic.ncodeunits iface s).val := by
        have := Int.mul_le_mul_of_nonneg_left hsz.2 h0
        omega
      have hprod_ge : (basic.ncodeunits iface s).val ≤
          (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val := by
        have := Int.mul_le_mul_of_nonneg_left hsz.1 h0
        omega
      have hval : (basic.sizeofString ops s).val =
          (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val := by
        unfold basic.sizeofString
        rw [hnc, hct, hcs]
        change wrapInt .i64 ((basic.ncodeunits iface s).val *
          ((basic.codeunit iface s).byteSize).val) = _
        exact wrapInt_i64_of_bounds _ ⟨by omega, by omega⟩
      exact ⟨hval, fun h1 => ⟨by omega, by omega⟩⟩

/-! ## Bounds checking -/

def CheckboundsIntegerArrayProperty : Prop :=
  (∀ (t : IntTy) (S R C CU CT Arr E : Type) (ops : StringOps S R C CU CT E)
      (items : Arr → List (JInt t)) (s : S) (indices : Arr),
    basic.checkboundsIntegerArray items
      (fun s (i : JInt t) => (.ok (basic.checkboundsScalar ops.ncodeunits
        (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
        (fun i n => JuliaLean.base.int.le i n) s i) : Except E Bool)) s indices =
      .ok (some ((items indices).all
        (fun i => decide (1 ≤ i.val) && decide (i.val ≤ (ops.ncodeunits s).val))))) ∧
  (∀ (t : IntTy) (S R C CU CT Arr E : Type) (ops : StringOps S R C CU CT E)
      (items : Arr → List (JInt t)) (s : S) (indices : Arr)
      (before : List (JInt t)) (bad : JInt t) (after : List (JInt t)),
    items indices = before ++ bad :: after →
    (∀ j ∈ before, 1 ≤ j.val ∧ j.val ≤ (ops.ncodeunits s).val) →
    ¬ (1 ≤ bad.val ∧ bad.val ≤ (ops.ncodeunits s).val) →
      basic.checkboundsIntegerArray items
        (fun s (i : JInt t) => (.ok (basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i) : Except E Bool)) s indices =
        .ok (some false)) ∧
  (∀ (S Arr I E : Type) (items : Arr → List I)
      (checkbounds : S → I → Except E Bool) (s : S) (indices : Arr)
      (before : List I) (failing : I) (after : List I) (err : E),
    items indices = before ++ failing :: after →
    (∀ j ∈ before, checkbounds s j = .ok true) →
    checkbounds s failing = .error err →
      basic.checkboundsIntegerArray items checkbounds s indices =
        .error (.predicate err))

theorem checkboundsIntegerArray_proven : CheckboundsIntegerArrayProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro t S R C CU CT Arr E ops items s indices
    have h := allPredicate_allAny_bool (E := E) items
      (fun i : JInt t => basic.checkboundsScalar ops.ncodeunits
        (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
        (fun i n => JuliaLean.base.int.le i n) s i) indices
    have hfun :
        (fun i : JInt t => basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i) =
        (fun i : JInt t => decide (1 ≤ i.val) && decide (i.val ≤ (ops.ncodeunits s).val)) := by
      funext i
      simp [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq]
    simpa [basic.checkboundsIntegerArray, hfun] using h
  · intro t S R C CU CT Arr E ops items s indices before bad after hitems hbef hout
    unfold basic.checkboundsIntegerArray JuliaLean.base.anyall.allPredicate
      JuliaLean.base.anyall.allAny
    rw [hitems]
    apply allAny_loop_shortCircuit
    · intro j hj
      rcases hbef j hj with ⟨h1, h2⟩
      simp [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq, h1, h2]
    · apply congrArg Except.ok
      simp only [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq,
        Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
  · intro S Arr I E items checkbounds s indices before failing after err hitems hbef hfail
    unfold basic.checkboundsIntegerArray JuliaLean.base.anyall.allPredicate
      JuliaLean.base.anyall.allAny
    rw [hitems]
    exact allAny_loop_error (checkbounds s) before failing after err false hbef hfail

def CheckboundsRealArrayProperty : Prop :=
  (∀ (S R C CU CT Arr RVal E : Type) (ops : StringOps S R C CU CT E)
      (items : Arr → List RVal)
      (atLeastOne : RVal → Bool) (atMostN : RVal → Index → Bool)
      (s : S) (indices : Arr),
    basic.checkboundsRealArray items
      (fun s r => (.ok (basic.checkboundsScalar ops.ncodeunits atLeastOne atMostN s r) :
        Except E Bool))
      s indices =
      .ok (some ((items indices).all
        (basic.checkboundsScalar ops.ncodeunits atLeastOne atMostN s)))) ∧
  (∀ (t : IntTy) (RNonInt S R C CU CT Arr E : Type) (ops : StringOps S R C CU CT E)
      (items : Arr → List (JInt t ⊕ RNonInt))
      (s : S) (indices : Arr)
      (before : List (JInt t)) (bad : JInt t) (after : List (JInt t ⊕ RNonInt)),
    items indices = before.map Sum.inl ++ (.inl bad) :: after →
    (∀ j ∈ before, 1 ≤ j.val ∧ j.val ≤ (ops.ncodeunits s).val) →
    ¬ (1 ≤ bad.val ∧ bad.val ≤ (ops.ncodeunits s).val) →
      basic.checkboundsRealArray items
        (fun s r => match r with
          | .inl i => .ok (basic.checkboundsScalar ops.ncodeunits
              (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
              (fun i n => JuliaLean.base.int.le i n) s i)
          | .inr _ => .error (ops.methodError "checkbounds"))
        s indices = .ok (some false)) ∧
  (∀ (t : IntTy) (RNonInt S R C CU CT Arr E : Type) (ops : StringOps S R C CU CT E)
      (items : Arr → List (JInt t ⊕ RNonInt))
      (s : S) (indices : Arr)
      (before : List (JInt t)) (x : RNonInt) (after : List (JInt t ⊕ RNonInt)),
    items indices = before.map Sum.inl ++ (.inr x) :: after →
    (∀ j ∈ before, 1 ≤ j.val ∧ j.val ≤ (ops.ncodeunits s).val) →
      basic.checkboundsRealArray items
        (fun s r => match r with
          | .inl i => .ok (basic.checkboundsScalar ops.ncodeunits
              (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
              (fun i n => JuliaLean.base.int.le i n) s i)
          | .inr _ => .error (ops.methodError "checkbounds"))
        s indices = .error (.predicate (ops.methodError "checkbounds")))

theorem checkboundsRealArray_proven : CheckboundsRealArrayProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro S R C CU CT Arr RVal E ops items atLeastOne atMostN s indices
    simpa [basic.checkboundsRealArray] using
      allPredicate_allAny_bool (E := E) items
        (basic.checkboundsScalar ops.ncodeunits atLeastOne atMostN s) indices
  · intro t RNonInt S R C CU CT Arr E ops items s indices before bad after hitems hbef hout
    unfold basic.checkboundsRealArray JuliaLean.base.anyall.allPredicate
      JuliaLean.base.anyall.allAny
    rw [hitems]
    apply allAny_loop_shortCircuit
    · intro r hr
      rcases List.mem_map.mp hr with ⟨j, hj, rfl⟩
      rcases hbef j hj with ⟨h1, h2⟩
      simp [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq, h1, h2]
    · apply congrArg Except.ok
      simp only [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq,
        Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
  · intro t RNonInt S R C CU CT Arr E ops items s indices before x after hitems hbef
    unfold basic.checkboundsRealArray JuliaLean.base.anyall.allPredicate
      JuliaLean.base.anyall.allAny
    rw [hitems]
    apply allAny_loop_error
    · intro r hr
      rcases List.mem_map.mp hr with ⟨j, hj, rfl⟩
      rcases hbef j hj with ⟨h1, h2⟩
      simp [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq, h1, h2]
    · rfl

def BoundsModelProperty : Prop :=
  CheckboundsIntegerArrayProperty ∧
  CheckboundsRealArrayProperty ∧
  (∀ (t : IntTy) (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i : JInt t),
    basic.checkboundsScalar ops.ncodeunits
      (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
      (fun i n => JuliaLean.base.int.le i n) s i = true ↔
      (1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val)) ∧
  (∀ (S R C CU CT E X I : Type) (ops : StringOps S R C CU CT E)
      (rangeOps : IntegerRangeOps X I E) (s : S) (r : X),
    rangeOps.isempty r = true →
      basic.checkboundsRange ops rangeOps s r = .ok true) ∧
  (∀ (S R C CU CT E X I : Type) (ops : StringOps S R C CU CT E)
      (rangeOps : IntegerRangeOps X I E) (s : S) (r : X) (lo : I),
    rangeOps.isempty r = false →
    rangeOps.minimum r = .ok lo →
    rangeOps.atLeastOne lo = false →
      basic.checkboundsRange ops rangeOps s r = .ok false) ∧
  (∀ (S R C CU CT E X I : Type) (ops : StringOps S R C CU CT E)
      (rangeOps : IntegerRangeOps X I E) (s : S) (r : X) (lo hi : I),
    rangeOps.isempty r = false →
    rangeOps.minimum r = .ok lo →
    rangeOps.atLeastOne lo = true →
    rangeOps.maximum r = .ok hi →
      basic.checkboundsRange ops rangeOps s r =
        .ok (rangeOps.atMostN hi (ops.ncodeunits s))) ∧
  (∀ (t : IntTy) (S R C CU CT E X : Type) (ops : StringOps S R C CU CT E)
      (isempty : X → Bool) (minimum maximum : X → Except E (JInt t))
      (s : S) (r : X) (lo hi : JInt t),
    let rangeOps : IntegerRangeOps X (JInt t) E :=
      { isempty := isempty
        minimum := minimum
        maximum := maximum
        atLeastOne := JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1)
        atMostN := fun i n => JuliaLean.base.int.le i n }
    isempty r = false →
    minimum r = .ok lo →
    maximum r = .ok hi →
      (basic.checkboundsRange ops rangeOps s r = .ok true ↔
        (1 ≤ lo.val ∧ hi.val ≤ (ops.ncodeunits s).val))) ∧
  (∀ (t : IntTy) (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (boundsErr : S → JInt t → E) (s : S) (i : JInt t),
    (1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val →
      basic.checkbounds
        (fun s (i : JInt t) => .ok (basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i))
        boundsErr s i = .ok ()) ∧
    (¬ (1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val) →
      basic.checkbounds
        (fun s (i : JInt t) => .ok (basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i))
        boundsErr s i = .error (boundsErr s i))) ∧
  (∀ (t : IntTy) (T S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (cu : CodeUnits T S) (i : JInt t),
    basic.codeUnitsCheckbounds
      (fun s (i : JInt t) => basic.checkboundsScalar ops.ncodeunits
        (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
        (fun i n => JuliaLean.base.int.le i n) s i) cu i = true ↔
      (1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits cu.s).val))

theorem boundsModel_proven : BoundsModelProperty := by
  refine ⟨checkboundsIntegerArray_proven, checkboundsRealArray_proven,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t S R C CU CT E ops s i
    simp [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq]
  · intro S R C CU CT E X I ops rangeOps s r hempty
    simp [basic.checkboundsRange, hempty]
  · intro S R C CU CT E X I ops rangeOps s r lo hnonempty hlo hfalse
    simp [basic.checkboundsRange, hnonempty, hlo, hfalse]
  · intro S R C CU CT E X I ops rangeOps s r lo hi hnonempty hlo htrue hhi
    simp [basic.checkboundsRange, hnonempty, hlo, htrue, hhi]
  · intro t S R C CU CT E X ops isempty minimum maximum s r lo hi rangeOps hnonempty hlo hhi
    unfold basic.checkboundsRange
    dsimp only [rangeOps]
    simp only [hnonempty, ↓reduceIte, hlo, bind_except_ok, int_le_one_eq, hhi,
      int_le_ncodeunits_eq, pure_except]
    by_cases h1 : 1 ≤ lo.val
    · simp [h1]
    · simp [h1]
  · intro t S R C CU CT E ops boundsErr s i
    constructor
    · intro h
      simp [basic.checkbounds, basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq, h.1, h.2]
    · intro h
      have hcb : basic.checkboundsScalar ops.ncodeunits
          (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
          (fun i n => JuliaLean.base.int.le i n) s i = false := by
        simp only [basic.checkboundsScalar, int_le_one_eq, int_le_ncodeunits_eq,
          Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      simp [basic.checkbounds, hcb]
  · intro t T S R C CU CT E ops cu i
    simp [basic.codeUnitsCheckbounds, basic.checkboundsScalar,
      int_le_one_eq, int_le_ncodeunits_eq]

/-! ## Character comparison and classification -/

def CmpStringProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (a b : S),
    ops.sameReference a b = true →
      basic.cmp ops a b = .ok (basic.int 0)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (a b : S) (charsA charsB : List C),
    ops.sameReference a b = false →
    IteratesTo ops a charsA →
    IteratesTo ops b charsB →
    basic.cmp ops a b =
      .ok (if SameCharacters ops.equalChar charsA charsB then basic.int 0
        else if LexicallyLess ops.equalChar ops.lessChar charsA charsB then basic.int (-1)
        else basic.int 1)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (a b : S) (err : E),
    ops.sameReference a b = false →
    ops.iterateFirst a = .error err →
      basic.cmp ops a b = .error err) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (a b : S) (c d : C) (i j : Index),
    ops.sameReference a b = false →
    ops.iterateFirst a = .ok (some (c, i)) →
    ops.iterateFirst b = .ok (some (d, j)) →
    ops.equalChar c d = false →
      basic.cmp ops a b =
        .ok (if ops.lessChar c d then basic.int (-1) else basic.int 1))

theorem cmpString_proven : CmpStringProperty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E ops a b hsame
    simp [basic.cmp, hsame]
  · intro S R C CU CT E ops a b charsA charsB hsame hcharsA hcharsB
    have hcmp := cmp_of_iteratesTo ops a b charsA charsB hsame hcharsA hcharsB
    rwa [lexCompare_dichotomy] at hcmp
  · intro S R C CU CT E ops a b err hsame hfail
    simp [basic.cmp, hsame, hfail]
  · intro S R C CU CT E ops a b c d i j hsame ha hb hneq
    unfold basic.cmp
    rw [hsame]
    simp only [Bool.false_eq_true, ↓reduceIte, ha, bind_except_ok, hb]
    cases ops.iterationBound a + ops.iterationBound b <;>
      cases hless : ops.lessChar c d <;>
      simp [basic.cmpLoop, hneq, hless, JuliaLean.base.operators.ifelseValue]

def EqStringProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (a b : S),
    ops.sameReference a b = true → basic.eq ops a b = .ok true) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (a b : S) (charsA charsB : List C),
    ops.sameReference a b = false →
    IteratesTo ops a charsA →
    IteratesTo ops b charsB →
    (basic.eq ops a b = .ok true ↔ SameCharacters ops.equalChar charsA charsB = true))

theorem eqString_proven : EqStringProperty := by
  constructor
  · intro S R C CU CT E ops a b hsame
    simp [basic.eq, basic.cmp, hsame]
  · intro S R C CU CT E ops a b charsA charsB hsame hcharsA hcharsB
    have hcmp := cmp_of_iteratesTo ops a b charsA charsB hsame hcharsA hcharsB
    have hzero := lexCompare_zero_iff ops.equalChar ops.lessChar charsA charsB
    simp [basic.eq, hcmp, hzero]

def IslessStringProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (a b : S),
    ops.sameReference a b = true → basic.isless ops a b = .ok false) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (a b : S) (charsA charsB : List C),
    ops.sameReference a b = false →
    IteratesTo ops a charsA →
    IteratesTo ops b charsB →
    (basic.isless ops a b = .ok true ↔
      LexicallyLess ops.equalChar ops.lessChar charsA charsB = true))

theorem islessString_proven : IslessStringProperty := by
  constructor
  · intro S R C CU CT E ops a b hsame
    simp [basic.isless, basic.cmp, hsame]
  · intro S R C CU CT E ops a b charsA charsB hsame hcharsA hcharsB
    have hcmp := cmp_of_iteratesTo ops a b charsA charsB hsame hcharsA hcharsB
    have hnegative := lexCompare_negative_iff ops.equalChar ops.lessChar charsA charsB
    simp [basic.isless, hcmp, hnegative]

def CmpSymbolProperty : Prop :=
  ∀ (Sym : Type) (strcmp : Sym → Sym → JInt .i32) (a b : Sym),
    ((basic.cmpSymbol strcmp a b).val < 0 ↔ (strcmp a b).val < 0) ∧
    ((basic.cmpSymbol strcmp a b).val = 0 ↔ (strcmp a b).val = 0) ∧
    (0 < (basic.cmpSymbol strcmp a b).val ↔ 0 < (strcmp a b).val) ∧
    (-1 ≤ (basic.cmpSymbol strcmp a b).val ∧ (basic.cmpSymbol strcmp a b).val ≤ 1)

theorem cmpSymbol_proven : CmpSymbolProperty := by
  intro Sym strcmp a b
  cases h : (strcmp a b).val with
  | ofNat n =>
      cases n <;>
        simp [basic.cmpSymbol, basic.int, JInt.lit, JInt.wrap, wrapInt,
          IntTy.min, IntTy.bits, IntTy.signed, h] <;> omega
  | negSucc n =>
      simp [basic.cmpSymbol, basic.int, JInt.lit, JInt.wrap, wrapInt,
        IntTy.min, IntTy.bits, IntTy.signed, h] <;> omega

def IslessSymbolProperty : Prop :=
  ∀ (Sym : Type) (strcmp : Sym → Sym → JInt .i32) (a b : Sym),
    basic.islessSymbol strcmp a b = decide ((strcmp a b).val < 0) ∧
    ((strcmp a b).val = 0 → basic.islessSymbol strcmp a b = false)

theorem islessSymbol_proven : IslessSymbolProperty := by
  intro Sym strcmp a b
  constructor
  · cases h : (strcmp a b).val with
    | ofNat n =>
        cases n <;>
          simp [basic.islessSymbol, basic.cmpSymbol, basic.int, JInt.lit,
            JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed, h] <;> omega
    | negSucc n =>
        simp [basic.islessSymbol, basic.cmpSymbol, basic.int, JInt.lit,
          JInt.wrap, wrapInt, IntTy.min, IntTy.bits, IntTy.signed, h] <;> omega
  · intro hzero
    simp [basic.islessSymbol, basic.cmpSymbol, hzero]

/-! ## ASCII classification (`isascii`, `_isascii`, `_isascii_chunks`) -/

private theorem uint32_zero_or (x : UInt32) : (0 : UInt32) ||| x = x := by
  apply UInt32.eq_of_toBitVec_eq
  change 0#32 ||| x.toBitVec = x.toBitVec
  simp

private theorem uint32_eq_of_toNat {a b : UInt32} (h : a.toNat = b.toNat) : a = b := by
  apply UInt32.eq_of_toBitVec_eq
  exact BitVec.eq_of_toNat_eq h

private theorem uint32_getLsbD_7_false_of_lt_128 (w : UInt32) (h : w < 0x80) :
    w.toBitVec.getLsbD 7 = false := by
  have hlt : w.toNat < 128 := h
  rw [← BitVec.testBit_toNat, show w.toBitVec.toNat = w.toNat from rfl,
    show (7 : Nat) = 0 + 7 from rfl, Nat.testBit_add]
  have hpow : (2 ^ 7 : Nat) = 128 := by decide
  have hdiv : w.toNat / 128 = 0 := by omega
  simp [hpow, hdiv]

private theorem uint32_shr24_getLsbD_7_of_ge (c : UInt32) (h : 0x80000000 ≤ c) :
    (c >>> 24).toBitVec.getLsbD 7 = true := by
  have hge : 2147483648 ≤ c.toNat := h
  have hlt : c.toNat < 4294967296 := c.toBitVec.isLt
  have h24 : (24 : UInt32).toNat % 32 = 24 := by decide
  have hshr : (c >>> 24).toNat = c.toNat / 16777216 := by
    rw [UInt32.toNat_shiftRight, h24, Nat.shiftRight_eq_div_pow]
  rw [← BitVec.testBit_toNat, show (c >>> 24).toBitVec.toNat = (c >>> 24).toNat from rfl,
    hshr, show (7 : Nat) = 0 + 7 from rfl, Nat.testBit_add]
  have hpow : (2 ^ 7 : Nat) = 128 := by decide
  have hdiv : c.toNat / 16777216 / 128 = 1 := by omega
  simp [hpow, hdiv]

private theorem isasciiChar_false_of_ge_0x80000000 (c : UInt32) (h : 0x80000000 ≤ c) :
    basic.isasciiChar c = false := by
  have hbit : (basic.bswap32 c).toBitVec.getLsbD 7 = true := by
    unfold basic.bswap32
    rw [UInt32.toBitVec_or, BitVec.getLsbD_or, uint32_shr24_getLsbD_7_of_ge c h, Bool.or_true]
  unfold basic.isasciiChar
  rw [decide_eq_false_iff_not]
  intro hlt
  have hf := uint32_getLsbD_7_false_of_lt_128 (basic.bswap32 c) hlt
  rw [hbit] at hf
  cases hf

private theorem isasciiChar_or_false_of_ge (x m : UInt32) (hm : 0x80000000 ≤ m) :
    basic.isasciiChar (x ||| m) = false := by
  apply isasciiChar_false_of_ge_0x80000000
  have hm_nat : 2147483648 ≤ m.toNat := hm
  have hlt_m : m.toNat < 4294967296 := m.toBitVec.isLt
  have hlt_or : (x ||| m).toNat < 4294967296 := (x ||| m).toBitVec.isLt
  have hbit_m : m.toBitVec.getLsbD 31 = true := by
    rw [← BitVec.testBit_toNat, show m.toBitVec.toNat = m.toNat from rfl,
      show (31 : Nat) = 0 + 31 from rfl, Nat.testBit_add]
    have hpow : (2 ^ 31 : Nat) = 2147483648 := by decide
    have hdiv : m.toNat / 2147483648 = 1 := by omega
    simp [hpow, hdiv]
  have hbit_or : (x ||| m).toBitVec.getLsbD 31 = true := by
    rw [show (x ||| m).toBitVec = x.toBitVec ||| m.toBitVec from rfl,
      BitVec.getLsbD_or, hbit_m, Bool.or_true]
  have htest : ((x ||| m).toNat / 2147483648) % 2 = 1 := by
    rw [← BitVec.testBit_toNat, show (x ||| m).toBitVec.toNat = (x ||| m).toNat from rfl,
      show (31 : Nat) = 0 + 31 from rfl, Nat.testBit_add] at hbit_or
    have hpow : (2 ^ 31 : Nat) = 2147483648 := by decide
    rw [hpow] at hbit_or
    simpa [Nat.testBit_zero] using hbit_or
  change 2147483648 ≤ (x ||| m).toNat
  omega

def IsasciiCharProperty : Prop :=
  (∀ (u c : UInt32),
    JuliaLean.base.char.char_UInt32 u = .ok c →
      basic.isasciiChar c = basic.isasciiAbstractChar id u ∧
      (basic.isasciiChar c = true ↔ u < 0x80) ∧
      (basic.isasciiChar c = false ↔ 0x80 ≤ u)) ∧
  (∀ (c u : UInt32),
    JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps c = .ok u →
      (basic.isasciiChar c = true → u < 0x80) ∧
      (0x80 ≤ u → basic.isasciiChar c = false)) ∧
  (∀ c : UInt32,
    0x80000000 ≤ c → basic.isasciiChar c = false) ∧
  (∀ c : UInt32,
    (c &&& 0xff) = 0 →
    ((c >>> 8) &&& 0xff) = 0 →
    ((c >>> 16) &&& 0xff) = 0 →
      basic.bswap32 c = c >>> 24 ∧
      (basic.isasciiChar c = true ↔ c >>> 24 < 0x80)) ∧
  (∀ u : UInt32,
    u < 0x100 →
      basic.bswap32 (u <<< 24) = u ∧
      (basic.isasciiChar (u <<< 24) = true ↔ u < 0x80)) ∧
  (∀ u : UInt32,
    0 < u → u < 0x100 →
      basic.bswap32 u = u <<< 24 ∧
      basic.isasciiChar u = false)

theorem isasciiChar_proven : IsasciiCharProperty := by
  have htrail : ∀ c : UInt32,
      (c &&& 0xff) = 0 →
      ((c >>> 8) &&& 0xff) = 0 →
      ((c >>> 16) &&& 0xff) = 0 →
        basic.bswap32 c = c >>> 24 ∧
        (basic.isasciiChar c = true ↔ c >>> 24 < 0x80) := by
    intro c hb0 hb1 hb2
    have hswap : basic.bswap32 c = c >>> 24 := by
      unfold basic.bswap32
      rw [hb0, hb1, hb2]
      have h0_24 : (0 : UInt32) <<< 24 = 0 := by decide
      have h0_16 : (0 : UInt32) <<< 16 = 0 := by decide
      have h0_8 : (0 : UInt32) <<< 8 = 0 := by decide
      rw [h0_24, h0_16, h0_8, uint32_zero_or, uint32_zero_or, uint32_zero_or]
    exact ⟨hswap, by simp [basic.isasciiChar, hswap]⟩
  have htop : ∀ u : UInt32,
      u < 0x100 →
        basic.bswap32 (u <<< 24) = u ∧
        (basic.isasciiChar (u <<< 24) = true ↔ u < 0x80) := by
    intro u hu
    have hu_nat : u.toNat < 256 := hu
    have h24 : (24 : UInt32).toNat % 32 = 24 := by decide
    have h8 : (8 : UInt32).toNat % 32 = 8 := by decide
    have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
    have hshl : (u <<< 24).toNat = u.toNat * 16777216 := by
      rw [UInt32.toNat_shiftLeft, h24, Nat.shiftLeft_eq]
      have hpow : 2 ^ 24 = 16777216 := by decide
      have hmod : 2 ^ 32 = 4294967296 := by decide
      rw [hpow, hmod]
      omega
    have hb0 : (u <<< 24) &&& 0xff = 0 := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_and]
      change (u <<< 24).toNat &&& 255 = 0
      rw [show (255 : Nat) = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, hshl]
      have : 2 ^ 8 = 256 := by decide
      omega
    have hb1 : ((u <<< 24) >>> 8) &&& 0xff = 0 := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_and]
      change ((u <<< 24) >>> 8).toNat &&& 255 = 0
      rw [show (255 : Nat) = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
        UInt32.toNat_shiftRight, h8, Nat.shiftRight_eq_div_pow, hshl]
      have : 2 ^ 8 = 256 := by decide
      omega
    have hb2 : ((u <<< 24) >>> 16) &&& 0xff = 0 := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_and]
      change ((u <<< 24) >>> 16).toNat &&& 255 = 0
      rw [show (255 : Nat) = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
        UInt32.toNat_shiftRight, h16, Nat.shiftRight_eq_div_pow, hshl]
      have : 2 ^ 16 = 65536 := by decide
      have : 2 ^ 8 = 256 := by decide
      omega
    have hb3 : (u <<< 24) >>> 24 = u := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_shiftRight, h24, Nat.shiftRight_eq_div_pow, hshl]
      have : 2 ^ 24 = 16777216 := by decide
      omega
    rcases htrail (u <<< 24) hb0 hb1 hb2 with ⟨hswap, hascii⟩
    rw [hb3] at hswap hascii
    exact ⟨hswap, hascii⟩
  refine ⟨?_, ?_, isasciiChar_false_of_ge_0x80000000, htrail, htop, ?_⟩
  · intro u c hchar
    unfold JuliaLean.base.char.char_UInt32 at hchar
    by_cases hu : u < 0x80
    · simp only [hu, ↓reduceIte, pure_except] at hchar
      have hceq : c = u <<< 24 := (Except.ok.inj hchar).symm
      subst hceq
      have hu100 : u < 0x100 := by
        change u.toNat < 256
        have : u.toNat < 128 := hu
        omega
      have htrue : basic.isasciiChar (u <<< 24) = true := (htop u hu100).2.mpr hu
      have habs : basic.isasciiAbstractChar id u = true := by
        simp [basic.isasciiAbstractChar, hu]
      have hnotge : ¬ (0x80 ≤ u) := by
        change ¬ (128 ≤ u.toNat)
        have : u.toNat < 128 := hu
        omega
      simp [htrue, habs, hu, hnotge]
    · simp only [hu, ↓reduceIte] at hchar
      by_cases hu2 : u < 0x00200000
      · simp only [hu2, ↓reduceIte, bind_except_ok, pure_except] at hchar
        have hge : 0x80 ≤ u := by
          change 128 ≤ u.toNat
          have : ¬ (u.toNat < 128) := hu
          omega
        have habs : basic.isasciiAbstractChar id u = false := by
          simp [basic.isasciiAbstractChar, hu]
        have hfalse : basic.isasciiChar c = false := by
          rcases Except.ok.inj hchar with rfl
          split
          · exact isasciiChar_or_false_of_ge _ 0xc0800000 (by decide)
          · split
            · exact isasciiChar_or_false_of_ge _ 0xe0808000 (by decide)
            · exact isasciiChar_or_false_of_ge _ 0xf0808080 (by decide)
        simp [hfalse, habs, hu, hge]
      · simp [hu2, JuliaLean.base.char.throw_code_point_err] at hchar
        cases hchar
  · intro c u hcp
    unfold JuliaLean.base.char.codepoint_Char JuliaLean.base.char.uint32_Char at hcp
    by_cases hlt : c < 0x80000000
    · simp only [hlt, ↓reduceIte, pure_except] at hcp
      have hueq : u = c >>> 24 := (Except.ok.inj hcp).symm
      have hu_lt : u < 0x80 := by
        rw [hueq]
        change (c >>> 24).toNat < 128
        have h24 : (24 : UInt32).toNat % 32 = 24 := by decide
        rw [UInt32.toNat_shiftRight, h24, Nat.shiftRight_eq_div_pow]
        have hc_lt : c.toNat < 2147483648 := hlt
        have : (2 ^ 24 : Nat) = 16777216 := by decide
        omega
      refine ⟨fun _ => hu_lt, fun hge => ?_⟩
      have h1 : u.toNat < 128 := hu_lt
      have h2 : 128 ≤ u.toNat := hge
      omega
    · have hge : 0x80000000 ≤ c := by
        change 2147483648 ≤ c.toNat
        have : ¬ (c.toNat < 2147483648) := hlt
        omega
      have hfalse := isasciiChar_false_of_ge_0x80000000 c hge
      simp [hfalse]
  · intro u hpos hu
    have hpos_nat : 0 < u.toNat := hpos
    have hu_nat : u.toNat < 256 := hu
    have h24 : (24 : UInt32).toNat % 32 = 24 := by decide
    have h8 : (8 : UInt32).toNat % 32 = 8 := by decide
    have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
    have hshl : (u <<< 24).toNat = u.toNat * 16777216 := by
      rw [UInt32.toNat_shiftLeft, h24, Nat.shiftLeft_eq]
      have hpow : 2 ^ 24 = 16777216 := by decide
      have hmod : 2 ^ 32 = 4294967296 := by decide
      rw [hpow, hmod]
      omega
    have hb0 : u &&& 0xff = u := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_and]
      change u.toNat &&& 255 = u.toNat
      rw [show (255 : Nat) = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
      have : 2 ^ 8 = 256 := by decide
      omega
    have hshr8 : u >>> 8 = 0 := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_shiftRight, h8, Nat.shiftRight_eq_div_pow]
      change u.toNat / 2 ^ 8 = 0
      have : 2 ^ 8 = 256 := by decide
      omega
    have hshr16 : u >>> 16 = 0 := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_shiftRight, h16, Nat.shiftRight_eq_div_pow]
      change u.toNat / 2 ^ 16 = 0
      have : 2 ^ 16 = 65536 := by decide
      omega
    have hshr24 : u >>> 24 = 0 := by
      apply uint32_eq_of_toNat
      rw [UInt32.toNat_shiftRight, h24, Nat.shiftRight_eq_div_pow]
      change u.toNat / 2 ^ 24 = 0
      have : 2 ^ 24 = 16777216 := by decide
      omega
    have hswap : basic.bswap32 u = u <<< 24 := by
      unfold basic.bswap32
      rw [hb0, hshr8, hshr16, hshr24]
      have h0 : ((0 : UInt32) &&& 0xff) <<< 16 = 0 := by decide
      have h1 : ((0 : UInt32) &&& 0xff) <<< 8 = 0 := by decide
      rw [h0, h1]
      apply UInt32.eq_of_toBitVec_eq
      change (u <<< 24).toBitVec ||| 0#32 ||| 0#32 ||| 0#32 = (u <<< 24).toBitVec
      simp
    refine ⟨hswap, ?_⟩
    unfold basic.isasciiChar
    rw [hswap, decide_eq_false_iff_not]
    intro hlt
    have hlt_nat : (u <<< 24).toNat < 128 := hlt
    omega

def IsasciiStringProperty : Prop :=
  (∀ (S C E : Type) (items : S → List C)
      (toUInt32 : C → UInt32) (s : S),
    basic.isasciiString items
      (fun c => (.ok (basic.isasciiAbstractChar toUInt32 c) : Except E Bool)) s =
      .ok (some ((items s).all (basic.isasciiAbstractChar toUInt32))) ∧
    (basic.isasciiString items
      (fun c => (.ok (basic.isasciiAbstractChar toUInt32 c) : Except E Bool)) s =
        .ok (some true) ↔
      ∀ c ∈ items s, toUInt32 c < 0x80)) ∧
  (∀ (S C E : Type) (items : S → List C)
      (isAscii : C → Except E Bool) (s : S)
      (before : List C) (bad : C) (after : List C),
    items s = before ++ bad :: after →
    (∀ c ∈ before, isAscii c = .ok true) →
    isAscii bad = .ok false →
      basic.isasciiString items isAscii s = .ok (some false)) ∧
  (∀ (S E : Type) (items : S → List basic.Char) (s : S),
    basic.isasciiString items
      (fun c => (.ok (basic.isasciiChar c) : Except E Bool)) s =
      .ok (some ((items s).all basic.isasciiChar)) ∧
    (basic.isasciiString items
      (fun c => (.ok (basic.isasciiChar c) : Except E Bool)) s = .ok (some true) ↔
      ∀ c ∈ items s, basic.bswap32 c < 0x80))

theorem isasciiString_proven : IsasciiStringProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro S C E items toUInt32 s
    have hall := allPredicate_allAny_bool (E := E) items
      (basic.isasciiAbstractChar toUInt32) s
    unfold basic.isasciiString
    rw [hall]
    exact ⟨rfl, by simp [List.all_eq_true, basic.isasciiAbstractChar]⟩
  · intro S C E items isAscii s before bad after hitems hbef hbad
    unfold basic.isasciiString JuliaLean.base.anyall.allPredicate
      JuliaLean.base.anyall.allAny
    rw [hitems]
    exact allAny_loop_shortCircuit isAscii before bad after false hbef hbad
  · intro S E items s
    have hall := allPredicate_allAny_bool (E := E) items basic.isasciiChar s
    unfold basic.isasciiString
    rw [hall]
    exact ⟨rfl, by simp [List.all_eq_true, basic.isasciiChar]⟩
def isAsciiCodeUnit {CU : Type} (cuOps : CodeUnitOps CU) (x : CU) : Bool :=
  decide (0 ≤ cuOps.toInt x ∧ cuOps.toInt x < 0x80)

private theorem bitvec8_getLsbD_7 (bv : BitVec 8) :
    bv.getLsbD 7 = decide (128 ≤ bv.toNat) := by
  have hlt : bv.toNat < 256 := bv.isLt
  rw [← BitVec.testBit_toNat, show (7 : Nat) = 0 + 7 by rfl, Nat.testBit_add]
  have hpow : (2 ^ 7 : Nat) = 128 := by decide
  rw [hpow]
  by_cases h128 : 128 ≤ bv.toNat
  · have hdiv : bv.toNat / 128 = 1 := by omega
    rw [hdiv]
    simp [h128]
  · have hdiv : bv.toNat / 128 = 0 := by omega
    rw [hdiv]
    simp [h128]

private theorem uint8_isAscii_eq_not_bit7 (a : UInt8) :
    isAsciiCodeUnit basic.uint8CodeUnitOps a = !a.toBitVec.getLsbD 7 := by
  rw [bitvec8_getLsbD_7]
  unfold isAsciiCodeUnit basic.uint8CodeUnitOps
  have hbt : a.toBitVec.toNat = a.toNat := rfl
  rw [hbt]
  by_cases h : a.toNat < 128
  · have h1 : (a.toNat : Int) < 128 := by omega
    have h2 : ¬ (128 ≤ a.toNat) := by omega
    simp [h1, h2]
  · have h1 : ¬ ((a.toNat : Int) < 128) := by omega
    have h2 : 128 ≤ a.toNat := by omega
    simp [h1, h2]

private theorem uint8_isAscii_iff_lt (a : UInt8) :
    isAsciiCodeUnit basic.uint8CodeUnitOps a = true ↔ a.toNat < 0x80 := by
  unfold isAsciiCodeUnit basic.uint8CodeUnitOps
  rw [decide_eq_true_eq]
  change (0 ≤ (a.toNat : Int) ∧ (a.toNat : Int) < 128) ↔ a.toNat < 128
  omega

private theorem uint8_bitor_ascii_iff (a b : UInt8) :
    isAsciiCodeUnit basic.uint8CodeUnitOps (basic.uint8CodeUnitOps.bitor a b) = true ↔
      (isAsciiCodeUnit basic.uint8CodeUnitOps a = true ∧
       isAsciiCodeUnit basic.uint8CodeUnitOps b = true) := by
  rw [uint8_isAscii_eq_not_bit7, uint8_isAscii_eq_not_bit7, uint8_isAscii_eq_not_bit7]
  dsimp [basic.uint8CodeUnitOps]
  rw [UInt8.toBitVec_or, BitVec.getLsbD_or]
  cases a.toBitVec.getLsbD 7 <;> cases b.toBitVec.getLsbD 7 <;> decide

private theorem asciiRangeLoop_uint8_iff (v : IndexedVector Index UInt8) (last : Index)
    (hmax : last.val < 9223372036854775807) :
    ∀ (fuel : Nat) (n : Index) (acc : UInt8),
      (n.val ≤ last.val → (last.val - n.val + 1).toNat ≤ fuel) →
      (isAsciiCodeUnit basic.uint8CodeUnitOps
        (basic.asciiRangeLoop basic.indexVectorOps basic.uint8CodeUnitOps v last fuel n acc) = true ↔
        (isAsciiCodeUnit basic.uint8CodeUnitOps acc = true ∧
         ∀ k : Index, n.val ≤ k.val ∧ k.val ≤ last.val →
           (v.get k).toNat < 0x80)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n acc hfuel
      have hnotle : ¬ (n.val ≤ last.val) := by omega
      unfold basic.asciiRangeLoop
      constructor
      · intro hacc
        refine ⟨hacc, ?_⟩
        intro k hk
        omega
      · exact fun h => h.1
  | succ fuel ih =>
      intro n acc hfuel
      unfold basic.asciiRangeLoop
      by_cases hle : n.val ≤ last.val
      · have hle' : basic.indexVectorOps.toInt n ≤ basic.indexVectorOps.toInt last := hle
        have hstep_val : (basic.indexVectorOps.add n (basic.indexVectorOps.ofInt 1)).val = n.val + 1 :=
          add_one_val n (by change n.val + 1 ≤ 9223372036854775807; omega)
        have hfuel' : (basic.indexVectorOps.add n (basic.indexVectorOps.ofInt 1)).val ≤ last.val →
            (last.val - (basic.indexVectorOps.add n (basic.indexVectorOps.ofInt 1)).val + 1).toNat ≤ fuel := by
          intro hnext
          omega
        simp only [hle', ite_true]
        rw [ih _ _ hfuel', uint8_bitor_ascii_iff, uint8_isAscii_iff_lt (v.get n), hstep_val]
        constructor
        · rintro ⟨⟨hacc, hn⟩, hrest⟩
          refine ⟨hacc, ?_⟩
          intro k ⟨hk1, hk2⟩
          by_cases heq : k.val = n.val
          · have hkeq : k = n := Subtype.ext heq
            subst hkeq
            exact hn
          · exact hrest k ⟨by omega, hk2⟩
        · rintro ⟨hacc, hall⟩
          refine ⟨⟨hacc, hall n ⟨Int.le_refl _, hle⟩⟩, ?_⟩
          intro k ⟨hk1, hk2⟩
          exact hall k ⟨by omega, hk2⟩
      · have hle' : ¬ (basic.indexVectorOps.toInt n ≤ basic.indexVectorOps.toInt last) := hle
        simp only [hle', ite_false]
        constructor
        · intro hacc
          refine ⟨hacc, ?_⟩
          intro k hk
          omega
        · exact fun h => h.1

theorem isasciiRange_uint8_iff (v : IndexedVector Index UInt8) (first last : Index)
    (hmax : last.val < IntTy.max .i64) :
    basic.isasciiRange basic.indexVectorOps basic.uint8CodeUnitOps v first last = true ↔
      (∀ k : Index, first.val ≤ k.val ∧ k.val ≤ last.val → (v.get k).toNat < 0x80) := by
  have hmax' : last.val < 9223372036854775807 := hmax
  change isAsciiCodeUnit basic.uint8CodeUnitOps
    (basic.asciiRangeLoop basic.indexVectorOps basic.uint8CodeUnitOps v last
      (basic.genericRangeSteps basic.indexVectorOps first last)
      first basic.uint8CodeUnitOps.zero) = true ↔ _
  have hfuel : first.val ≤ last.val →
      (last.val - first.val + 1).toNat ≤ basic.genericRangeSteps basic.indexVectorOps first last := by
    intro hle
    simp [basic.genericRangeSteps, basic.indexVectorOps, hle]
  have hzero : isAsciiCodeUnit basic.uint8CodeUnitOps basic.uint8CodeUnitOps.zero = true := by
    decide
  rw [asciiRangeLoop_uint8_iff v last hmax' _ first _ hfuel]
  simp [hzero]

theorem isasciiRange_uint8_false_iff (v : IndexedVector Index UInt8) (first last : Index)
    (hmax : last.val < IntTy.max .i64) :
    basic.isasciiRange basic.indexVectorOps basic.uint8CodeUnitOps v first last = false ↔
      (∃ k : Index, first.val ≤ k.val ∧ k.val ≤ last.val ∧ 0x80 ≤ (v.get k).toNat) := by
  rw [Bool.eq_false_iff, ne_eq, isasciiRange_uint8_iff v first last hmax]
  constructor
  · intro hnot
    rcases Classical.not_forall.mp hnot with ⟨k, hk⟩
    by_cases hrange : first.val ≤ k.val ∧ k.val ≤ last.val
    · refine ⟨k, hrange.1, hrange.2, ?_⟩
      have hnotlt : ¬ ((v.get k).toNat < 0x80) := fun hlt => hk (fun _ => hlt)
      omega
    · exfalso
      exact hk (fun hr => False.elim (hrange hr))
  · rintro ⟨k, hk1, hk2, hge⟩ hall
    have hlt := hall k ⟨hk1, hk2⟩
    omega

private theorem asciiChunksLoop_uint8_true (v : IndexedVector Index UInt8) (chunk last : Index)
    (hchunk : 1 ≤ chunk.val)
    (hlast : last.val + chunk.val ≤ 9223372036854775807)
    (hmin : -9223372036854775808 ≤ last.val - chunk.val)
    (htail : ∀ k : Index, (last - chunk + basic.int 1).val ≤ k.val ∧ k.val ≤ last.val →
      (v.get k).toNat < 0x80) :
    ∀ (m : Nat) (n : Index),
      -9223372036854775808 + chunk.val ≤ n.val →
      (n.val ≤ (last - chunk).val → ((last - chunk).val - n.val + 1).toNat ≤ m) →
      (∀ k : Index, n.val ≤ k.val ∧ k.val ≤ last.val → (v.get k).toNat < 0x80) →
      basic.asciiChunksLoop basic.indexVectorOps basic.uint8CodeUnitOps v chunk last m n =
        true := by
  have hl := index_bounds last
  have hc := index_bounds chunk
  have hsub_val : (last - chunk).val = last.val - chunk.val := by
    change wrapInt .i64 (last.val - chunk.val) = last.val - chunk.val
    exact wrapInt_i64_of_bounds (last.val - chunk.val) ⟨hmin, by omega⟩
  have hmax : last.val < IntTy.max .i64 := by
    change last.val < 9223372036854775807
    omega
  intro m
  induction m with
  | zero =>
      intro n _ _ _
      unfold basic.asciiChunksLoop
      rw [isasciiRange_uint8_iff v _ last hmax]
      exact htail
  | succ m ih =>
      intro n hnmin hle hall
      have hn := index_bounds n
      unfold basic.asciiChunksLoop
      by_cases hcond : basic.indexVectorOps.toInt n ≤
          basic.indexVectorOps.toInt (basic.indexVectorOps.sub last chunk)
      · have hcond' : n.val ≤ last.val - chunk.val := by
          change n.val ≤ (last - chunk).val at hcond
          omega
        have hnext_val : (n + chunk).val = n.val + chunk.val := by
          change wrapInt .i64 (n.val + chunk.val) = n.val + chunk.val
          exact wrapInt_i64_of_bounds (n.val + chunk.val) ⟨by omega, by omega⟩
        have hend_val : (n + chunk - basic.int 1).val = n.val + chunk.val - 1 := by
          change wrapInt .i64 ((n + chunk).val - 1) = n.val + chunk.val - 1
          rw [hnext_val]
          exact wrapInt_i64_of_bounds (n.val + chunk.val - 1) ⟨by omega, by omega⟩
        have hchunk_ok :
            basic.isasciiRange basic.indexVectorOps basic.uint8CodeUnitOps v n
              (basic.indexVectorOps.sub (basic.indexVectorOps.add n chunk)
                (basic.indexVectorOps.ofInt 1)) = true := by
          rw [isasciiRange_uint8_iff v n _
            (by change (n + chunk - basic.int 1).val < 9223372036854775807; omega)]
          intro k ⟨hk1, hk2⟩
          change k.val ≤ (n + chunk - basic.int 1).val at hk2
          exact hall k ⟨hk1, by omega⟩
        have hfuel' : (n + chunk).val ≤ (last - chunk).val →
            ((last - chunk).val - (n + chunk).val + 1).toNat ≤ m := by
          intro hnext_le
          have h1 := hle (by change n.val ≤ (last - chunk).val; omega)
          omega
        have hrec := ih (n + chunk) (by omega) hfuel'
          (fun k ⟨hk1, hk2⟩ => hall k ⟨by omega, hk2⟩)
        simp only [hcond, ↓reduceIte, hchunk_ok, Bool.not_true, Bool.false_eq_true]
        exact hrec
      · simp only [hcond, ↓reduceIte]
        rw [isasciiRange_uint8_iff v _ last hmax]
        exact htail

def IsasciiVectorProperty : Prop :=
  (∀ (C : Type) (toUInt32 : C → UInt32) (c : C),
    (basic.isasciiAbstractChar toUInt32 c = true ↔ toUInt32 c < 0x80) ∧
    (basic.isasciiAbstractChar toUInt32 c = false ↔ 0x80 ≤ toUInt32 c)) ∧
  (∀ (v : IndexedVector Index UInt8) (first last : Index),
    last.val < IntTy.max .i64 →
      (basic.isasciiRange basic.indexVectorOps basic.uint8CodeUnitOps v first last = true ↔
        ∀ k : Index, first.val ≤ k.val ∧ k.val ≤ last.val → (v.get k).toNat < 0x80) ∧
      (basic.isasciiRange basic.indexVectorOps basic.uint8CodeUnitOps v first last = false ↔
        ∃ k : Index, first.val ≤ k.val ∧ k.val ≤ last.val ∧ 0x80 ≤ (v.get k).toNat)) ∧
  (∀ (v : IndexedVector Index UInt8) (chunk first last : Index),
    1 ≤ chunk.val →
    IntTy.min .i64 + chunk.val ≤ first.val →
    first.val + chunk.val - 1 ≤ last.val →
    last.val + chunk.val ≤ IntTy.max .i64 →
    (∀ k : Index, first.val ≤ k.val ∧ k.val ≤ last.val → (v.get k).toNat < 0x80) →
      basic.isasciiChunks basic.indexVectorOps basic.uint8CodeUnitOps v chunk first last =
        true) ∧
  (∀ (v : IndexedVector Index UInt8) (chunk first last : Index),
    1 ≤ chunk.val →
    IntTy.min .i64 + chunk.val ≤ first.val →
    first.val ≤ last.val - chunk.val →
    last.val + chunk.val ≤ IntTy.max .i64 →
    (∃ k : Index, first.val ≤ k.val ∧ k.val ≤ first.val + chunk.val - 1 ∧
      0x80 ≤ (v.get k).toNat) →
      basic.isasciiChunks basic.indexVectorOps basic.uint8CodeUnitOps v chunk first last =
        false) ∧
  (∀ (v : IndexedVector Index UInt8),
    1 ≤ v.firstindex.val →
    v.firstindex.val ≤ v.lastindex.val →
    v.lastindex.val + 1024 ≤ IntTy.max .i64 →
    (∀ k : Index, v.firstindex.val ≤ k.val ∧ k.val ≤ v.lastindex.val →
      (v.get k).toNat < 0x80) →
      basic.isasciiVector basic.indexVectorOps basic.uint8CodeUnitOps v = true) ∧
  (∀ (v : IndexedVector Index UInt8),
    1 ≤ v.firstindex.val →
    v.lastindex.val - v.firstindex.val + 1 < 1536 →
    v.lastindex.val < IntTy.max .i64 →
    (∃ k : Index, v.firstindex.val ≤ k.val ∧ k.val ≤ v.lastindex.val ∧
      0x80 ≤ (v.get k).toNat) →
      basic.isasciiVector basic.indexVectorOps basic.uint8CodeUnitOps v = false) ∧
  (∀ (v : IndexedVector Index UInt8),
    1 ≤ v.firstindex.val →
    1536 ≤ v.lastindex.val - v.firstindex.val + 1 →
    v.lastindex.val + 1024 ≤ IntTy.max .i64 →
    (∃ k : Index, v.firstindex.val ≤ k.val ∧ k.val ≤ v.firstindex.val + 1023 ∧
      0x80 ≤ (v.get k).toNat) →
      basic.isasciiVector basic.indexVectorOps basic.uint8CodeUnitOps v = false)

theorem isasciiVector_proven : IsasciiVectorProperty := by
  have hchunks_true : ∀ (v : IndexedVector Index UInt8) (chunk first last : Index),
      1 ≤ chunk.val →
      IntTy.min .i64 + chunk.val ≤ first.val →
      first.val + chunk.val - 1 ≤ last.val →
      last.val + chunk.val ≤ IntTy.max .i64 →
      (∀ k : Index, first.val ≤ k.val ∧ k.val ≤ last.val → (v.get k).toNat < 0x80) →
        basic.isasciiChunks basic.indexVectorOps basic.uint8CodeUnitOps v chunk first last =
          true := by
    intro v chunk first last hchunk hmin hspan hmax hall
    have hf := index_bounds first
    have hl := index_bounds last
    have hc := index_bounds chunk
    have hmin' : -9223372036854775808 + chunk.val ≤ first.val := hmin
    have hmax' : last.val + chunk.val ≤ 9223372036854775807 := hmax
    have hsub_val : (last - chunk).val = last.val - chunk.val := by
      change wrapInt .i64 (last.val - chunk.val) = last.val - chunk.val
      exact wrapInt_i64_of_bounds (last.val - chunk.val) ⟨by omega, by omega⟩
    have htail_start : (last - chunk + basic.int 1).val = last.val - chunk.val + 1 := by
      change wrapInt .i64 ((last - chunk).val + 1) = last.val - chunk.val + 1
      rw [hsub_val]
      exact wrapInt_i64_of_bounds (last.val - chunk.val + 1) ⟨by omega, by omega⟩
    unfold basic.isasciiChunks
    exact asciiChunksLoop_uint8_true v chunk last hchunk hmax' (by omega)
      (fun k ⟨hk1, hk2⟩ => hall k ⟨by omega, hk2⟩)
      (basic.genericRangeSteps basic.indexVectorOps first (last - chunk))
      first hmin'
      (fun hle => by simp [basic.genericRangeSteps, basic.indexVectorOps, hle])
      hall
  have hchunks_false : ∀ (v : IndexedVector Index UInt8) (chunk first last : Index),
      1 ≤ chunk.val →
      IntTy.min .i64 + chunk.val ≤ first.val →
      first.val ≤ last.val - chunk.val →
      last.val + chunk.val ≤ IntTy.max .i64 →
      (∃ k : Index, first.val ≤ k.val ∧ k.val ≤ first.val + chunk.val - 1 ∧
        0x80 ≤ (v.get k).toNat) →
        basic.isasciiChunks basic.indexVectorOps basic.uint8CodeUnitOps v chunk first last =
          false := by
    intro v chunk first last hchunk hmin hcond hmax hex
    have hf := index_bounds first
    have hl := index_bounds last
    have hc := index_bounds chunk
    have hmin' : -9223372036854775808 + chunk.val ≤ first.val := hmin
    have hmax' : last.val + chunk.val ≤ 9223372036854775807 := hmax
    have hsub_val : (last - chunk).val = last.val - chunk.val := by
      change wrapInt .i64 (last.val - chunk.val) = last.val - chunk.val
      exact wrapInt_i64_of_bounds (last.val - chunk.val) ⟨by omega, by omega⟩
    have hnext_val : (first + chunk).val = first.val + chunk.val := by
      change wrapInt .i64 (first.val + chunk.val) = first.val + chunk.val
      exact wrapInt_i64_of_bounds (first.val + chunk.val) ⟨by omega, by omega⟩
    have hend_val : (first + chunk - basic.int 1).val = first.val + chunk.val - 1 := by
      change wrapInt .i64 ((first + chunk).val - 1) = first.val + chunk.val - 1
      rw [hnext_val]
      exact wrapInt_i64_of_bounds (first.val + chunk.val - 1) ⟨by omega, by omega⟩
    have hcond' : basic.indexVectorOps.toInt first ≤
        basic.indexVectorOps.toInt (basic.indexVectorOps.sub last chunk) := by
      change first.val ≤ (last - chunk).val
      omega
    have hfalse :
        basic.isasciiRange basic.indexVectorOps basic.uint8CodeUnitOps v first
          (basic.indexVectorOps.sub (basic.indexVectorOps.add first chunk)
            (basic.indexVectorOps.ofInt 1)) = false := by
      rw [isasciiRange_uint8_false_iff v first _
        (by change (first + chunk - basic.int 1).val < 9223372036854775807; omega)]
      rcases hex with ⟨k, hk1, hk2, hge⟩
      exact ⟨k, hk1, by change k.val ≤ (first + chunk - basic.int 1).val; omega, hge⟩
    unfold basic.isasciiChunks
    cases hsteps : basic.genericRangeSteps basic.indexVectorOps first
        (basic.indexVectorOps.sub last chunk) with
    | zero =>
        simp [basic.genericRangeSteps, hcond'] at hsteps
        change (last - chunk).val - first.val + 1 ≤ 0 at hsteps
        omega
    | succ fuel =>
        simp [basic.asciiChunksLoop, hcond', hfalse]
  refine ⟨?_, ?_, hchunks_true, hchunks_false, ?_, ?_, ?_⟩
  · intro C toUInt32 c
    refine ⟨?_, ?_⟩
    · simp [basic.isasciiAbstractChar]
    · simp only [basic.isasciiAbstractChar, decide_eq_false_iff_not]
      constructor
      · intro h
        have h' : ¬ ((toUInt32 c).toNat < 128) := h
        change 128 ≤ (toUInt32 c).toNat
        omega
      · intro h hlt
        have h' : 128 ≤ (toUInt32 c).toNat := h
        have hlt' : (toUInt32 c).toNat < 128 := hlt
        omega
  · intro v first last hmax
    exact ⟨isasciiRange_uint8_iff v first last hmax,
      isasciiRange_uint8_false_iff v first last hmax⟩
  · intro v h1 hle hmax hall
    have hf := index_bounds v.firstindex
    have hl := index_bounds v.lastindex
    have hmax' : v.lastindex.val + 1024 ≤ 9223372036854775807 := hmax
    have hlen_val : (v.lastindex - v.firstindex + basic.int 1).val =
        v.lastindex.val - v.firstindex.val + 1 := by
      have hsub : (v.lastindex - v.firstindex).val = v.lastindex.val - v.firstindex.val := by
        change wrapInt .i64 (v.lastindex.val - v.firstindex.val) =
          v.lastindex.val - v.firstindex.val
        exact wrapInt_i64_of_bounds (v.lastindex.val - v.firstindex.val) ⟨by omega, by omega⟩
      change wrapInt .i64 ((v.lastindex - v.firstindex).val + 1) =
        v.lastindex.val - v.firstindex.val + 1
      rw [hsub]
      exact wrapInt_i64_of_bounds (v.lastindex.val - v.firstindex.val + 1) ⟨by omega, by omega⟩
    dsimp [basic.isasciiVector]
    split
    · exact (isasciiRange_uint8_iff v v.firstindex v.lastindex
        (by change v.lastindex.val < 9223372036854775807; omega)).mpr hall
    · rename_i hge
      have hge' : 1536 ≤ v.lastindex.val - v.firstindex.val + 1 := by
        change ¬ ((v.lastindex - v.firstindex + basic.int 1).val < 1536) at hge
        omega
      have h1024 : (basic.indexVectorOps.ofInt 1024).val = 1024 := by decide
      exact hchunks_true v (basic.indexVectorOps.ofInt 1024) v.firstindex v.lastindex
        (by decide) (by rw [h1024]; change -9223372036854775808 + 1024 ≤ v.firstindex.val; omega)
        (by rw [h1024]; omega) (by rw [h1024]; exact hmax) hall
  · intro v h1 hshort hmax hex
    have hf := index_bounds v.firstindex
    have hl := index_bounds v.lastindex
    have hmax' : v.lastindex.val < 9223372036854775807 := hmax
    have hlen_val : (v.lastindex - v.firstindex + basic.int 1).val =
        v.lastindex.val - v.firstindex.val + 1 := by
      rcases hex with ⟨k, hk1, hk2, _⟩
      have hsub : (v.lastindex - v.firstindex).val = v.lastindex.val - v.firstindex.val := by
        change wrapInt .i64 (v.lastindex.val - v.firstindex.val) =
          v.lastindex.val - v.firstindex.val
        exact wrapInt_i64_of_bounds (v.lastindex.val - v.firstindex.val) ⟨by omega, by omega⟩
      change wrapInt .i64 ((v.lastindex - v.firstindex).val + 1) =
        v.lastindex.val - v.firstindex.val + 1
      rw [hsub]
      exact wrapInt_i64_of_bounds (v.lastindex.val - v.firstindex.val + 1) ⟨by omega, by omega⟩
    have hlt : basic.indexVectorOps.toInt
        (basic.indexVectorOps.add (basic.indexVectorOps.sub v.lastindex v.firstindex)
          (basic.indexVectorOps.ofInt 1)) <
        basic.indexVectorOps.toInt (basic.indexVectorOps.ofInt 1536) := by
      change (v.lastindex - v.firstindex + basic.int 1).val < 1536
      omega
    dsimp [basic.isasciiVector]
    simp only [hlt, ite_true]
    exact (isasciiRange_uint8_false_iff v v.firstindex v.lastindex hmax).mpr hex
  · intro v h1 hlong hmax hex
    have hf := index_bounds v.firstindex
    have hl := index_bounds v.lastindex
    have hmax' : v.lastindex.val + 1024 ≤ 9223372036854775807 := hmax
    have hlen_val : (v.lastindex - v.firstindex + basic.int 1).val =
        v.lastindex.val - v.firstindex.val + 1 := by
      have hsub : (v.lastindex - v.firstindex).val = v.lastindex.val - v.firstindex.val := by
        change wrapInt .i64 (v.lastindex.val - v.firstindex.val) =
          v.lastindex.val - v.firstindex.val
        exact wrapInt_i64_of_bounds (v.lastindex.val - v.firstindex.val) ⟨by omega, by omega⟩
      change wrapInt .i64 ((v.lastindex - v.firstindex).val + 1) =
        v.lastindex.val - v.firstindex.val + 1
      rw [hsub]
      exact wrapInt_i64_of_bounds (v.lastindex.val - v.firstindex.val + 1) ⟨by omega, by omega⟩
    have hnotlt : ¬ (basic.indexVectorOps.toInt
        (basic.indexVectorOps.add (basic.indexVectorOps.sub v.lastindex v.firstindex)
          (basic.indexVectorOps.ofInt 1)) <
        basic.indexVectorOps.toInt (basic.indexVectorOps.ofInt 1536)) := by
      change ¬ ((v.lastindex - v.firstindex + basic.int 1).val < 1536)
      omega
    have h1024 : (basic.indexVectorOps.ofInt 1024).val = 1024 := by decide
    dsimp [basic.isasciiVector]
    simp only [hnotlt, ite_false]
    exact hchunks_false v (basic.indexVectorOps.ofInt 1024) v.firstindex v.lastindex
      (by decide) (by rw [h1024]; change -9223372036854775808 + 1024 ≤ v.firstindex.val; omega)
      (by rw [h1024]; omega) (by rw [h1024]; exact hmax)
      (by rcases hex with ⟨k, hk1, hk2, hge⟩; exact ⟨k, hk1, by rw [h1024]; omega, hge⟩)

/-! ## Character index arithmetic (`length`, `thisind`, `prevind`, `nextind`, `reverseind`) -/

private theorem thisindLoop_rewind {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) (j : Index)
    (hj1 : 1 ≤ j.val)
    (hjok : j.val = 1 ∨ ops.isvalid s j = .ok true)
    (hinv : ∀ k : Index, j.val < k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok false) :
    ∀ (fuel : Nat) (i : Index),
      j.val ≤ i.val →
      i.val ≤ (ops.ncodeunits s).val →
      i.val - j.val ≤ (fuel : Int) →
      basic.thisindLoop ops s fuel i = .ok j := by
  intro fuel
  induction fuel with
  | zero =>
      intro i hji _ hfuel
      have heq : i = j := by
        apply Subtype.ext
        omega
      rw [heq]
      rfl
  | succ fuel ih =>
      intro i hji hile hfuel
      unfold basic.thisindLoop
      by_cases hgt1 : 1 < i.val
      · by_cases heq : i.val = j.val
        · have hij : i = j := Subtype.ext heq
          subst hij
          rcases hjok with h1 | hval
          · omega
          · simp [hgt1, hval]
        · have hlt : j.val < i.val := by omega
          have hval : ops.isvalid s i = .ok false := hinv i ⟨hlt, hile⟩
          have hi_b := index_bounds i
          have hi'_val : (i - basic.int 1).val = i.val - 1 := by
            change wrapInt .i64 (i.val - 1) = i.val - 1
            exact wrapInt_i64_of_bounds (i.val - 1) ⟨by omega, by omega⟩
          have hfuel' : (i - basic.int 1).val - j.val ≤ (fuel : Int) := by
            have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
            omega
          have hrec := ih (i - basic.int 1) (by omega) (by omega) hfuel'
          simp [hgt1, hval, hrec]
      · have heq : i = j := Subtype.ext (by omega)
        rw [if_neg hgt1, heq]
        rfl

private theorem thisindInt_rewind {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) (i j : Index)
    (hj1 : 1 ≤ j.val) (hji : j.val ≤ i.val) (hile : i.val ≤ (ops.ncodeunits s).val)
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hjok : j.val = 1 ∨ ops.isvalid s j = .ok true)
    (hinv : ∀ k : Index, j.val < k.val ∧ k.val ≤ i.val → ops.isvalid s k = .ok false) :
    basic.thisindInt ops s i = .ok j := by
  have hz := add_one_val (ops.ncodeunits s) hmax
  have hne : (i.val == (ops.ncodeunits s + basic.int 1).val) = false := by
    rw [hz, beq_eq_false_iff_ne]
    omega
  have hin : (decide (0 ≤ i.val) && decide (i.val ≤ (ops.ncodeunits s + basic.int 1).val)) = true := by
    rw [hz]
    simp [show 0 ≤ i.val by omega, show i.val ≤ (ops.ncodeunits s).val + 1 by omega]
  have hloop : ∀ (fuel : Nat) (m : Index),
      j.val ≤ m.val → m.val ≤ i.val → m.val - j.val ≤ (fuel : Int) →
      basic.thisindLoop ops s fuel m = .ok j := by
    intro fuel
    induction fuel with
    | zero =>
        intro m hjm _ hfuel
        have heq : m = j := Subtype.ext (by omega)
        rw [heq]
        rfl
    | succ fuel ih =>
        intro m hjm hmle hfuel
        unfold basic.thisindLoop
        by_cases hgt1 : 1 < m.val
        · by_cases heq : m.val = j.val
          · have hmj : m = j := Subtype.ext heq
            subst hmj
            rcases hjok with h1 | hval
            · omega
            · simp [hgt1, hval]
          · have hlt : j.val < m.val := by omega
            have hval : ops.isvalid s m = .ok false := hinv m ⟨hlt, hmle⟩
            have hm_b := index_bounds m
            have hm'_val : (m - basic.int 1).val = m.val - 1 := by
              change wrapInt .i64 (m.val - 1) = m.val - 1
              exact wrapInt_i64_of_bounds (m.val - 1) ⟨by omega, by omega⟩
            have hfuel' : (m - basic.int 1).val - j.val ≤ (fuel : Int) := by
              have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
              omega
            have hrec := ih (m - basic.int 1) (by omega) (by omega) hfuel'
            simp [hgt1, hval, hrec]
        · have heq : m = j := Subtype.ext (by omega)
          rw [if_neg hgt1, heq]
          rfl
  have hres := hloop (i.val.toNat + 1) i hji (Int.le_refl _) (by omega)
  simpa [basic.thisindInt, hne, hin] using hres

private theorem lengthLoop_allValid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) (last : Index)
    (hlast : last.val ≤ (ops.ncodeunits s).val)
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true) :
    ∀ (fuel : Nat) (current count : Index),
      1 ≤ current.val →
      current.val ≤ last.val + 1 →
      last.val - current.val + 1 ≤ (fuel : Int) →
      0 ≤ count.val →
      count.val + (last.val - current.val + 1) ≤ 9223372036854775807 →
      basic.lengthLoop ops s last fuel current count =
        .ok (basic.int (count.val + (last.val - current.val + 1))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro current count _ hle hfuel hc0 hcmax
      have heq : last.val - current.val + 1 = 0 := by omega
      have hce : count = basic.int (count.val + (last.val - current.val + 1)) := by
        apply Subtype.ext
        change count.val = wrapInt .i64 (count.val + (last.val - current.val + 1))
        rw [heq, Int.add_zero]
        exact (wrapInt_of_inRange .i64 count.val count.property).symm
      simpa [basic.lengthLoop] using congrArg (Except.ok (ε := E)) hce
  | succ fuel ih =>
      intro current count hcur1 hle hfuel hc0 hcmax
      unfold basic.lengthLoop
      by_cases hcond : current.val ≤ last.val
      · have hval : ops.isvalid s current = .ok true := hvalid current ⟨hcur1, by omega⟩
        have hcur_next : (current + basic.int 1).val = current.val + 1 :=
          add_one_val current (by change current.val + 1 ≤ 9223372036854775807; omega)
        have hcnt_next : (count + basic.boolInt true).val = count.val + 1 :=
          add_one_val count (by change count.val + 1 ≤ 9223372036854775807; omega)
        have hfuel' : last.val - (current + basic.int 1).val + 1 ≤ (fuel : Int) := by
          have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
          omega
        have hrec := ih (current + basic.int 1) (count + basic.boolInt true)
          (by omega) (by omega) hfuel' (by omega) (by omega)
        have hsum : (count + basic.boolInt true).val +
            (last.val - (current + basic.int 1).val + 1) =
            count.val + (last.val - current.val + 1) := by omega
        rw [hsum] at hrec
        simp [hcond, hval, hrec]
      · have heq : last.val - current.val + 1 = 0 := by omega
        have hce : count = basic.int (count.val + (last.val - current.val + 1)) := by
          apply Subtype.ext
          change count.val = wrapInt .i64 (count.val + (last.val - current.val + 1))
          rw [heq, Int.add_zero]
          exact (wrapInt_of_inRange .i64 count.val count.property).symm
        simp [hcond, ← hce]

def LengthProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i j : Index),
    i.val ≤ 0 →
      basic.lengthInt ops s i j = .error (ops.boundsError s i)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i j : Index),
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    ¬ (0 < i.val ∧ i.val ≤ (ops.ncodeunits s).val + 1) →
      basic.lengthInt ops s i j = .error (ops.boundsError s i)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i j : Index),
    0 < i.val ∧ i.val ≤ (ops.ncodeunits s + basic.int 1).val →
    j.val < 0 →
      basic.lengthInt ops s i j = .error (ops.boundsError s j)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i j : Index),
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    0 < i.val ∧ i.val ≤ (ops.ncodeunits s).val + 1 →
    ¬ (0 ≤ j.val ∧ j.val < (ops.ncodeunits s).val + 1) →
      basic.lengthInt ops s i j = .error (ops.boundsError s j)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i j : Index),
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    0 < i.val ∧ i.val ≤ (ops.ncodeunits s).val + 1 →
    0 ≤ j.val ∧ j.val < (ops.ncodeunits s).val + 1 →
    j.val < i.val →
      basic.lengthInt ops s i j = .ok (basic.int 0)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i : Index) (v : Bool),
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val →
    ops.isvalid s i = .ok v →
      basic.lengthInt ops s i i = .ok (basic.boolInt v)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i j : Index),
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    1 ≤ i.val ∧ i.val ≤ j.val ∧ j.val ≤ (ops.ncodeunits s).val →
    (∀ k : Index, i.val ≤ k.val ∧ k.val ≤ j.val → ops.isvalid s k = .ok false) →
      basic.lengthInt ops s i j = .ok (basic.int 0)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (s : S) (i j : Index),
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    (∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val → ops.isvalid s k = .ok true) →
    1 ≤ i.val ∧ i.val ≤ j.val ∧ j.val ≤ (ops.ncodeunits s).val →
      basic.lengthInt ops s i j = .ok (basic.int (j.val - i.val + 1)) ∧
      basic.lengthString ops (basic.lengthInt ops) s = .ok (ops.ncodeunits s)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (s : S),
    ops.ncodeunits s = basic.int 0 →
      basic.lengthString ops (basic.lengthInt ops) s = .ok (basic.int 0)) ∧
  (∀ (t : IntTy) (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (s : S) (i j : JInt t),
    IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 →
    IntTy.min .i64 ≤ j.val ∧ j.val ≤ IntTy.max .i64 →
      basic.lengthInteger ops (JuliaLean.base.int.convert .i64) s i j =
        basic.lengthInt ops s (basic.int i.val) (basic.int j.val))

theorem length_proven : LengthProperty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E ops s i j hi0
    have hnot : ¬ (0 < i.val) := by omega
    simp [basic.lengthInt, hnot]
  · intro S R C CU CT E ops s i j hmax hbad
    have hz := add_one_val (ops.ncodeunits s) hmax
    by_cases hpos : 0 < i.val
    · have hnotle : ¬ (i.val ≤ (ops.ncodeunits s + basic.int 1).val) := by omega
      simp [basic.lengthInt, hpos, hnotle]
    · simp [basic.lengthInt, hpos]
  · intro S R C CU CT E ops s i j hi hj0
    have hnot : ¬ (0 ≤ j.val) := by omega
    simp [basic.lengthInt, hi.1, hi.2, hnot]
  · intro S R C CU CT E ops s i j hmax hi hbad
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hi2 : i.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    by_cases hj0 : 0 ≤ j.val
    · have hnotlt : ¬ (j.val < (ops.ncodeunits s + basic.int 1).val) := by omega
      simp [basic.lengthInt, hi.1, hi2, hj0, hnotlt]
    · simp [basic.lengthInt, hi.1, hi2, hj0]
  · intro S R C CU CT E ops s i j hmax hi hj hlt
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hi2 : i.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    have hj2 : j.val < (ops.ncodeunits s + basic.int 1).val := by omega
    have hnotle : ¬ (i.val ≤ j.val) := by omega
    have hsteps : basic.rangeSteps i j = 0 := by
      simp [basic.rangeSteps, hnotle]
    simp [basic.lengthInt, hi.1, hi2, hj.1, hj2, hsteps, basic.lengthLoop]
  · intro S R C CU CT E ops s i v hmax hi hvalid
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hi1 : 0 < i.val := by omega
    have hi2 : i.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    have hj1 : 0 ≤ i.val := by omega
    have hj2 : i.val < (ops.ncodeunits s + basic.int 1).val := by omega
    have hsteps : basic.rangeSteps i i = 1 := by
      unfold basic.rangeSteps
      simp
    have hzero_add : basic.int 0 + basic.boolInt v = basic.boolInt v := by
      cases v <;> decide
    simp [basic.lengthInt, hi1, hi2, hj1, hj2, hsteps, basic.lengthLoop, hvalid, hzero_add]
  · intro S R C CU CT E ops s i j hmax ⟨hi1, hij, hj_nc⟩ hall_false
    have hmax' : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807 := hmax
    have hz := add_one_val (ops.ncodeunits s) hmax'
    have hi0 : 0 < i.val := by omega
    have hi2 : i.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    have hj1 : 0 ≤ j.val := by omega
    have hj2 : j.val < (ops.ncodeunits s + basic.int 1).val := by omega
    have hloop : ∀ (fuel : Nat) (current : Index),
        i.val ≤ current.val →
        current.val ≤ j.val + 1 →
        j.val - current.val + 1 ≤ (fuel : Int) →
        basic.lengthLoop ops s j fuel current (basic.int 0) = .ok (basic.int 0) := by
      intro fuel
      induction fuel with
      | zero =>
          intro _ _ _ _
          rfl
      | succ fuel ih =>
          intro current hcur0 hle hfuel
          unfold basic.lengthLoop
          by_cases hcond : current.val ≤ j.val
          · have hcur_b := index_bounds current
            have hj_b := index_bounds j
            have hval : ops.isvalid s current = .ok false := hall_false current ⟨hcur0, hcond⟩
            have hcur_next : (current + basic.int 1).val = current.val + 1 :=
              add_one_val current (by change current.val + 1 ≤ 9223372036854775807; omega)
            have hfuel' : j.val - (current + basic.int 1).val + 1 ≤ (fuel : Int) := by
              have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
              omega
            have hrec := ih (current + basic.int 1) (by omega) (by omega) hfuel'
            have h00 : basic.int 0 + basic.boolInt false = basic.int 0 := by decide
            simp [hcond, hval, h00, hrec]
          · simp [hcond]
    have hsteps : (j.val - i.val + 1 : Int) ≤ (basic.rangeSteps i j : Int) := by
      unfold basic.rangeSteps
      simp only [hij, ↓reduceIte]
      omega
    have hl := hloop (basic.rangeSteps i j) i (Int.le_refl _) (by omega) hsteps
    simp [basic.lengthInt, hi0, hi2, hj1, hj2, hl]
  · intro S R C CU CT E ops s i j hmax hvalid ⟨hi1, hij, hj_nc⟩
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hmax' : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807 := hmax
    have hlen_ij : basic.lengthInt ops s i j = .ok (basic.int (j.val - i.val + 1)) := by
      have hi0 : 0 < i.val := by omega
      have hi2 : i.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
      have hj1 : 0 ≤ j.val := by omega
      have hj2 : j.val < (ops.ncodeunits s + basic.int 1).val := by omega
      have hsteps : (j.val - i.val + 1 : Int) ≤ (basic.rangeSteps i j : Int) := by
        unfold basic.rangeSteps
        simp only [hij, ↓reduceIte]
        omega
      have hl := lengthLoop_allValid ops s j hj_nc hmax' hvalid
        (basic.rangeSteps i j) i (basic.int 0) hi1 (by omega) hsteps (by decide)
        (by have := index_bounds j; have := index_bounds i; change 0 + (j.val - i.val + 1) ≤ 9223372036854775807; omega)
      have h0_val : (basic.int 0).val = 0 := rfl
      rw [h0_val, Int.zero_add] at hl
      simp [basic.lengthInt, hi0, hi2, hj1, hj2, hl]
    refine ⟨hlen_ij, ?_⟩
    unfold basic.lengthString
    have hpos_nc : 1 ≤ (ops.ncodeunits s).val := by omega
    have h1_pos : 0 < (basic.int 1).val := by decide
    have h1_le : (basic.int 1).val ≤ (ops.ncodeunits s + basic.int 1).val := by
      change 1 ≤ (ops.ncodeunits s + basic.int 1).val
      omega
    have hnc0 : 0 ≤ (ops.ncodeunits s).val := by omega
    have hnc_lt : (ops.ncodeunits s).val < (ops.ncodeunits s + basic.int 1).val := by omega
    have hsteps1 : ((ops.ncodeunits s).val - (basic.int 1).val + 1 : Int) ≤
        (basic.rangeSteps (basic.int 1) (ops.ncodeunits s) : Int) := by
      have h1le : (basic.int 1).val ≤ (ops.ncodeunits s).val := hpos_nc
      unfold basic.rangeSteps
      simp only [h1le, ↓reduceIte]
      have : (basic.int 1).val = 1 := rfl
      omega
    have hl1 := lengthLoop_allValid ops s (ops.ncodeunits s) (Int.le_refl _) hmax' hvalid
      (basic.rangeSteps (basic.int 1) (ops.ncodeunits s)) (basic.int 1) (basic.int 0)
      (Int.le_refl 1) (by change 1 ≤ (ops.ncodeunits s).val + 1; omega) hsteps1 (by decide)
      (by have := index_bounds (ops.ncodeunits s); change 0 + ((ops.ncodeunits s).val - 1 + 1) ≤ 9223372036854775807; omega)
    have h0_val : (basic.int 0).val = 0 := rfl
    have hnc_eq : basic.int (0 + ((ops.ncodeunits s).val - (basic.int 1).val + 1)) =
        ops.ncodeunits s := by
      apply Subtype.ext
      change wrapInt .i64 (0 + ((ops.ncodeunits s).val - 1 + 1)) = (ops.ncodeunits s).val
      have hsub : 0 + ((ops.ncodeunits s).val - 1 + 1) = (ops.ncodeunits s).val := by omega
      rw [hsub]
      exact wrapInt_of_inRange .i64 (ops.ncodeunits s).val (ops.ncodeunits s).property
    rw [h0_val, hnc_eq] at hl1
    have h1_le' : 1 ≤ (ops.ncodeunits s + basic.int 1).val := h1_le
    simp [basic.lengthInt, h1_le', hnc0, hnc_lt, hl1]
  · intro S R C CU CT E ops s hempty
    have h1 : basic.int 0 + basic.int 1 = basic.int 1 := by decide
    simp [basic.lengthString, basic.lengthInt, hempty, h1, basic.rangeSteps, basic.lengthLoop]
  · intro t S R C CU CT ops s i j hi hj
    rw [basic.lengthInteger, convert_i64_of_inRange i hi, convert_i64_of_inRange j hj]
    rfl

def ThisindReverseindProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (s : S),
    0 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
      basic.thisindInt ops s (basic.int 0) = .ok (basic.int 0) ∧
      basic.thisindInt ops s (ops.ncodeunits s + basic.int 1) =
        .ok (ops.ncodeunits s + basic.int 1)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (s : S),
    1 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
      basic.thisindInt ops s (basic.int 1) = .ok (basic.int 1)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (s : S) (i : Index),
    0 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    ¬ (0 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val + 1) →
      basic.thisindInt ops s i = .error (ops.boundsError s i)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (s : S) (i : Index),
    1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val →
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    ops.isvalid s i = .ok true →
      basic.thisindInt ops s i = .ok i) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E) (s : S) (i j : Index),
    1 ≤ j.val ∧ j.val ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val →
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    (j.val = 1 ∨ ops.isvalid s j = .ok true) →
    (∀ k : Index, j.val < k.val ∧ k.val ≤ i.val → ops.isvalid s k = .ok false) →
      basic.thisindInt ops s i = .ok j) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (j : Index),
    (ops.ncodeunits s = basic.int 0 →
      basic.lastindexString (basic.modelStringOps ops intString) s = .ok (basic.int 0)) ∧
    (1 ≤ j.val ∧ j.val ≤ (ops.ncodeunits s).val →
      (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
      (j.val = 1 ∨ ops.isvalid s j = .ok true) →
      (∀ k : Index, j.val < k.val ∧ k.val ≤ (ops.ncodeunits s).val → ops.isvalid s k = .ok false) →
        basic.lastindexString (basic.modelStringOps ops intString) s = .ok j)) ∧
  (∀ (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S),
    0 ≤ (ops.ncodeunits s).val →
      basic.reverseindString (basic.modelStringOps ops intString)
        JuliaLean.base.int.sub
        (fun x => JuliaLean.base.int.add x (JuliaLean.base.int.lit .i64 1))
        (JuliaLean.base.int.convert .i64) s (basic.int 1) =
        basic.lastindexString (basic.modelStringOps ops intString) s) ∧
  (∀ (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S),
    1 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
      basic.reverseindString (basic.modelStringOps ops intString)
        JuliaLean.base.int.sub
        (fun x => JuliaLean.base.int.add x (JuliaLean.base.int.lit .i64 1))
        (JuliaLean.base.int.convert .i64) s (ops.ncodeunits s) = .ok (basic.int 1)) ∧
  (∀ (S R C CU CT E I D : Type) (ops : StringOps S R C CU CT E)
      (sub : Index → I → D) (addOne : D → D) (toInt : D → Except E Index)
      (s : S) (i : I),
    (∀ idx : Index,
      toInt (addOne (sub (ops.ncodeunits s) i)) = .ok idx →
      basic.reverseindString ops sub addOne toInt s i = ops.thisind s idx) ∧
    (∀ err : E,
      toInt (addOne (sub (ops.ncodeunits s) i)) = .error err →
      basic.reverseindString ops sub addOne toInt s i = .error err)) ∧
  (∀ (t : IntTy) (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S) (i : JInt t),
    (IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 →
      basic.thisindInteger (basic.modelStringOps ops intString)
        (JuliaLean.base.int.convert .i64) s i =
        basic.thisindInt (basic.modelStringOps ops intString) s (basic.int i.val)) ∧
    (¬ (IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64) →
      basic.thisindInteger (basic.modelStringOps ops intString)
        (JuliaLean.base.int.convert .i64) s i =
        .error (.inexactError "Int64")))

theorem thisindReverseind_proven : ThisindReverseindProperty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E ops s h0 hmax
    have hz := add_one_val (ops.ncodeunits s) hmax
    constructor
    · have hne : ¬ (0 = (ops.ncodeunits s + basic.int 1).val) := by omega
      have hle : 0 ≤ (ops.ncodeunits s + basic.int 1).val := by omega
      simp [basic.thisindInt, hne, hle, basic.thisindLoop]
    · simp [basic.thisindInt]
  · intro S R C CU CT E ops s h1 hmax
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hne : ¬ (1 = (ops.ncodeunits s + basic.int 1).val) := by omega
    have hle : 1 ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    simp [basic.thisindInt, hne, hle, basic.thisindLoop]
  · intro S R C CU CT E ops s i _ hmax hout
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hne : (i.val == (ops.ncodeunits s + basic.int 1).val) = false := by
      rw [hz, beq_eq_false_iff_ne]
      omega
    have hin : (decide (0 ≤ i.val) && decide (i.val ≤ (ops.ncodeunits s + basic.int 1).val)) = false := by
      rw [hz, Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      omega
    simp [basic.thisindInt, hne, hin]
  · intro S R C CU CT E ops s i hi hmax hvalid
    exact thisindInt_rewind ops s i i hi.1 (Int.le_refl _) hi.2 hmax
      (.inr hvalid) (fun k ⟨hk1, hk2⟩ => by omega)
  · intro S R C CU CT E ops s i j ⟨hj1, hji, hile⟩ hmax hjok hinv
    exact thisindInt_rewind ops s i j hj1 hji hile hmax hjok hinv
  · intro S R C CU CT E ops intString s j
    constructor
    · intro hempty
      have h1 : basic.int 0 + basic.int 1 = basic.int 1 := by decide
      simp [basic.lastindexString, basic.thisindInt, hempty, h1, basic.thisindLoop]
    · intro ⟨hj1, hjle⟩ hmax hjok hinv
      change basic.thisindInt ops s (ops.ncodeunits s) = .ok j
      exact thisindInt_rewind ops s (ops.ncodeunits s) j hj1 hjle (Int.le_refl _) hmax hjok hinv
  · intro S R C CU CT ops intString s h0
    have hlit : JuliaLean.base.int.lit .i64 1 = basic.int 1 := rfl
    rw [basic.reverseindString, basic.thisindInteger, modelStringOps_ncodeunits,
      int_sub_eq_sub, int_add_eq_add, hlit,
      sub_one_add_one (ops.ncodeunits s) h0, convert_i64_self (ops.ncodeunits s)]
    rfl
  · intro S R C CU CT ops intString s h1 hmax
    have hlit : JuliaLean.base.int.lit .i64 1 = basic.int 1 := rfl
    have hself : ops.ncodeunits s - ops.ncodeunits s + basic.int 1 = basic.int 1 := by
      apply Subtype.ext
      change wrapInt .i64 (wrapInt .i64 ((ops.ncodeunits s).val - (ops.ncodeunits s).val) + 1) = 1
      simp [wrapInt_of_inRange .i64 0 (by decide), wrapInt_of_inRange .i64 1 (by decide)]
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hne : ¬ (1 = (ops.ncodeunits s + basic.int 1).val) := by omega
    have hle : 1 ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    rw [basic.reverseindString, basic.thisindInteger, modelStringOps_ncodeunits,
      int_sub_eq_sub, int_add_eq_add, hlit]
    simp [hself, convert_i64_self (basic.int 1), basic.thisindInt, hne, hle, basic.thisindLoop]
  · intro S R C CU CT E I D ops sub addOne toInt s i
    constructor
    · intro idx hto
      simp [basic.reverseindString, basic.thisindInteger, hto]
    · intro err hto
      simp [basic.reverseindString, basic.thisindInteger, hto]
  · intro t S R C CU CT ops intString s i
    constructor
    · intro hin
      rw [basic.thisindInteger, convert_i64_of_inRange i hin, thisindInt_modelStringOps]
      simp
    · intro hout
      rw [basic.thisindInteger, convert_i64_of_outOfRange i hout]
      rfl

def NextindFirstProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (i n : Index),
    n.val < 0 →
      basic.nextindInt (basic.modelStringOps ops intString) intString s i n =
        .error (ops.argumentError ("n cannot be negative: " ++ intString n))) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (i n : Index),
    0 ≤ n.val → ¬ (0 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s).val) →
      basic.nextindInt (basic.modelStringOps ops intString) intString s i n =
        .error (ops.boundsError s i)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S),
    0 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
      basic.nextindInt (basic.modelStringOps ops intString) intString s
        (basic.int 0) (basic.int 0) = .ok (basic.int 0)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (n : Index),
    0 ≤ (ops.ncodeunits s).val → 1 ≤ n.val →
    (ops.ncodeunits s).val + n.val ≤ IntTy.max .i64 →
      basic.nextindInt (basic.modelStringOps ops intString) intString s (ops.ncodeunits s) n =
        .ok (ops.ncodeunits s + n) ∧
      (ops.ncodeunits s).val < (ops.ncodeunits s + n).val) ∧
  (∀ (t : IntTy) (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S) (n : JInt t) (last : Index),
    (basic.modelStringOps ops intString).lastindex s = .ok last →
    IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 →
    n.val < 0 →
      basic.firstN (basic.modelStringOps ops intString)
        (basic.nextindInt (basic.modelStringOps ops intString) intString)
        (JuliaLean.base.int.convert .i64) s n =
        .error (ops.argumentError ("n cannot be negative: " ++ intString (basic.int n.val)))) ∧
  (∀ (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S) (last : Index),
    0 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    0 ≤ last.val →
    (basic.modelStringOps ops intString).lastindex s = .ok last →
      basic.firstN (basic.modelStringOps ops intString)
        (basic.nextindInt (basic.modelStringOps ops intString) intString)
        (JuliaLean.base.int.convert .i64) s (basic.int 0) =
        ops.getindexSlice s (basic.int 1) (basic.int 0)) ∧
  (∀ (t : IntTy) (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S) (i n : JInt t),
    IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 →
    IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 →
      basic.nextindIntegerN (basic.modelStringOps ops intString)
        (JuliaLean.base.int.convert .i64) s i n =
        basic.nextindInt (basic.modelStringOps ops intString) intString s
          (basic.int i.val) (basic.int n.val) ∧
      basic.nextindInteger (basic.modelStringOps ops intString)
        (JuliaLean.base.int.convert .i64) s i =
        basic.nextindOne (basic.modelStringOps ops intString) s (basic.int i.val))

theorem nextindFirst_proven : NextindFirstProperty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E ops intString s i n hneg
    simp [basic.nextindInt, hneg]
  · intro S R C CU CT E ops intString s i n hn hout
    have hnotneg : ¬ (n.val < 0) := by omega
    simp [basic.nextindInt, hnotneg]
    intro hpos hle
    have hle' : i.val ≤ (ops.ncodeunits s).val := of_decide_eq_true hle
    omega
  · intro S R C CU CT E ops intString s h0 hmax
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hne : ¬ (0 = (ops.ncodeunits s + basic.int 1).val) := by omega
    have hle : 0 ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    simp [basic.nextindInt, basic.thisindInt, h0, hne, hle, basic.thisindLoop]
  · intro S R C CU CT E ops intString s n h0 hn hmax
    have hnotneg : ¬ (n.val < 0) := by omega
    have hne0 : ¬ (n.val = 0) := by omega
    have hsum : (ops.ncodeunits s + n).val = (ops.ncodeunits s).val + n.val := by
      have hz := index_bounds (ops.ncodeunits s)
      have hn' := index_bounds n
      have hmax' : (ops.ncodeunits s).val + n.val ≤ 9223372036854775807 := hmax
      change wrapInt .i64 ((ops.ncodeunits s).val + n.val) = (ops.ncodeunits s).val + n.val
      exact wrapInt_i64_of_bounds ((ops.ncodeunits s).val + n.val) (by omega)
    constructor
    · simp [basic.nextindInt, h0, hnotneg, hne0, Int.sub_self, basic.nextindLoop]
    · omega
  · intro t S R C CU CT ops intString s n last hlast hin hneg
    unfold basic.firstN
    rw [hlast, convert_i64_of_inRange n hin]
    have hneg' : (basic.int n.val).val < 0 := by
      change wrapInt .i64 n.val < 0
      rw [wrapInt_of_inRange .i64 n.val hin]
      exact hneg
    simp [basic.nextindInt, hneg']
  · intro S R C CU CT ops intString s last h0 hmax hlast0 hlast
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hne : ¬ (0 = (ops.ncodeunits s + basic.int 1).val) := by omega
    have hle : 0 ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    have hnext0 : basic.nextindInt (basic.modelStringOps ops intString) intString s
        (basic.int 0) (basic.int 0) = .ok (basic.int 0) := by
      simp [basic.nextindInt, basic.thisindInt, h0, hne, hle, basic.thisindLoop]
    have hmin :
        JuliaLean.base.operators.min
          (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
          JuliaLean.base.operators.ifelseValue last (basic.int 0) = basic.int 0 := by
      rw [operators_min_index]
      have h0_val : (basic.int 0).val = 0 := rfl
      by_cases hlt : (basic.int 0).val < last.val
      · exact if_pos hlt
      · rw [if_neg hlt]
        apply Subtype.ext
        change last.val = 0
        omega
    unfold basic.firstN
    rw [hlast, convert_i64_self (basic.int 0)]
    simp only [bind_except_ok, hnext0, hmin]
    rfl
  · intro t S R C CU CT ops intString s i n hi hn
    rw [basic.nextindIntegerN, basic.nextindInteger,
      convert_i64_of_inRange i hi, convert_i64_of_inRange n hn, nextindInt_modelStringOps]
    simp [basic.nextindOne]
private theorem previndLoop_allValid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true) :
    ∀ (fuel : Nat) (i n : Index),
      1 ≤ i.val →
      i.val ≤ (ops.ncodeunits s).val + 1 →
      0 ≤ n.val →
      i.val - 1 ≤ (fuel : Int) →
      -9223372036854775808 ≤ i.val - n.val →
      basic.previndLoop ops s fuel i n = .ok (basic.int (i.val - n.val)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i n hi1 _ hn0 hfuel hmin
      have hsub : i - n = basic.int (i.val - n.val) := rfl
      simp [basic.previndLoop, hsub]
  | succ fuel ih =>
      intro i n hi1 hile hn0 hfuel hmin
      unfold basic.previndLoop
      by_cases hcond : 0 < n.val ∧ 1 < i.val
      · have hi_b := index_bounds i
        have hn_b := index_bounds n
        have hi'_val : (i - basic.int 1).val = i.val - 1 := by
          change wrapInt .i64 (i.val - 1) = i.val - 1
          exact wrapInt_i64_of_bounds (i.val - 1) ⟨by omega, by omega⟩
        have hval_i' : ops.isvalid s (i - basic.int 1) = .ok true :=
          hvalid (i - basic.int 1) ⟨by omega, by omega⟩
        have hn'_val : (n - basic.boolInt true).val = n.val - 1 := by
          change wrapInt .i64 (n.val - 1) = n.val - 1
          exact wrapInt_i64_of_bounds (n.val - 1) ⟨by omega, by omega⟩
        have hfuel' : (i - basic.int 1).val - 1 ≤ (fuel : Int) := by
          have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
          omega
        have hrec := ih (i - basic.int 1) (n - basic.boolInt true)
          (by omega) (by omega) (by omega) hfuel' (by omega)
        have heq_diff : (i - basic.int 1).val - (n - basic.boolInt true).val = i.val - n.val := by
          omega
        rw [heq_diff] at hrec
        simp [hcond.1, hcond.2, hval_i', hrec]
      · have hcond' : (decide (0 < n.val) && decide (1 < i.val)) = false := by
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
          omega
        have hsub : i - n = basic.int (i.val - n.val) := rfl
        simp [hcond', hsub]

private theorem thisindInt_of_allValid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) (i : Index)
    (_h0 : 0 ≤ (ops.ncodeunits s).val)
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true)
    (hi0 : 0 ≤ i.val) (hile : i.val ≤ (ops.ncodeunits s + basic.int 1).val) :
    basic.thisindInt ops s i = .ok i := by
  have hz := add_one_val (ops.ncodeunits s) hmax
  by_cases heq : i.val = (ops.ncodeunits s + basic.int 1).val
  · have hbeq : (i.val == (ops.ncodeunits s + basic.int 1).val) = true := beq_iff_eq.mpr heq
    simp [basic.thisindInt, hbeq]
  · have hbeq : (i.val == (ops.ncodeunits s + basic.int 1).val) = false := beq_eq_false_iff_ne.mpr heq
    have hin : (decide (0 ≤ i.val) && decide (i.val ≤ (ops.ncodeunits s + basic.int 1).val)) = true := by
      simp [hi0, hile]
    by_cases hgt1 : 1 < i.val
    · have hval : ops.isvalid s i = .ok true := hvalid i ⟨by omega, by omega⟩
      simp [basic.thisindInt, hbeq, hin, basic.thisindLoop, hgt1, hval]
    · simp [basic.thisindInt, hbeq, hin, basic.thisindLoop, hgt1]

private theorem lastindex_of_allValid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S)
    (h0 : 0 ≤ (ops.ncodeunits s).val)
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true) :
    (basic.modelStringOps ops intString).lastindex s = .ok (ops.ncodeunits s) := by
  have hz := add_one_val (ops.ncodeunits s) hmax
  exact thisindInt_of_allValid ops s (ops.ncodeunits s) h0 hmax hvalid h0 (by omega)

private theorem previndInt_of_allValid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i n : Index)
    (h0 : 0 ≤ (ops.ncodeunits s).val)
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true)
    (hi1 : 1 ≤ i.val) (hile : i.val ≤ (ops.ncodeunits s + basic.int 1).val)
    (hn0 : 0 ≤ n.val) (hmin : -9223372036854775808 ≤ i.val - n.val) :
    basic.previndInt (basic.modelStringOps ops intString) intString s i n =
      .ok (basic.int (i.val - n.val)) := by
  have hi_b := index_bounds i
  rw [previndInt_modelStringOps]
  unfold basic.previndInt
  rw [previndLoop_thisindOps]
  have hnotneg : ¬ (n.val < 0) := by omega
  have hpos : 0 < i.val := by omega
  by_cases hn_zero : n.val = 0
  · have hthis := thisindInt_of_allValid ops s i h0 hmax hvalid (by omega) hile
    have heq : i = basic.int (i.val - n.val) := by
      apply Subtype.ext
      change i.val = wrapInt .i64 (i.val - n.val)
      rw [hn_zero, Int.sub_zero, wrapInt_of_inRange .i64 i.val i.property]
    rw [← heq]
    simp [hpos, hile, hn_zero, hthis]
  · have hloop := previndLoop_allValid ops s hvalid (i.val.toNat - 1) i n
      hi1 (by have := add_one_val (ops.ncodeunits s) hmax; omega) hn0 (by omega) hmin
    simp [hnotneg, hpos, hile, hn_zero, hloop]

private theorem nextindInt_one_of_allValid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i : Index)
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true)
    (hi0 : 0 ≤ i.val) (hile : i.val ≤ (ops.ncodeunits s).val) :
    basic.nextindInt (basic.modelStringOps ops intString) intString s i (basic.int 1) =
      .ok (i + basic.int 1) := by
  rw [nextindInt_modelStringOps]
  unfold basic.nextindInt
  simp only [nextindLoop_thisindOps]
  by_cases hlt : i.val < (ops.ncodeunits s).val
  · have hstep_val : (i + basic.int 1).val = i.val + 1 :=
      add_one_val i (by change i.val + 1 ≤ 9223372036854775807; omega)
    have hval1 : ops.isvalid s (i + basic.int 1) = .ok true :=
      hvalid (i + basic.int 1) ⟨by omega, by omega⟩
    have h1sub1 : basic.int 1 - basic.boolInt true = basic.int 0 := by decide
    have hadd0 : i + basic.int 1 + basic.int 0 = i + basic.int 1 := by
      apply Subtype.ext
      change wrapInt .i64 ((i + basic.int 1).val + 0) = (i + basic.int 1).val
      rw [Int.add_zero]
      exact wrapInt_of_inRange .i64 (i + basic.int 1).val (i + basic.int 1).property
    cases hfuel : ((ops.ncodeunits s).val - i.val).toNat with
    | zero => omega
    | succ fuel =>
        cases fuel <;>
          simp [hi0, hile, basic.nextindLoop, hlt, hval1, h1sub1, hadd0]
  · have hfuel : ((ops.ncodeunits s).val - i.val).toNat = 0 := by omega
    simp [hi0, hile, hfuel, basic.nextindLoop]

private theorem charListPrimOps_isvalid {C : Type} (defaultChar : C) (chars : List C)
    (k : Index) (h : 1 ≤ k.val ∧ k.val ≤ ((basic.charListPrimOps defaultChar).ncodeunits chars).val) :
    (basic.charListPrimOps defaultChar).isvalid chars k = .ok true := by
  rcases h with ⟨hk1, hk2⟩
  change k.val ≤ (basic.int (chars.length : Int)).val at hk2
  have hk_b := index_bounds k
  have hle : k.val ≤ (chars.length : Int) := by
    by_cases hfit : (chars.length : Int) ≤ 9223372036854775807
    · have hw : (basic.int (chars.length : Int)).val = (chars.length : Int) := by
        change wrapInt .i64 (chars.length : Int) = (chars.length : Int)
        exact wrapInt_i64_of_bounds (chars.length : Int) ⟨by omega, hfit⟩
      omega
    · omega
  simp [basic.charListPrimOps, hk1, hle]

private theorem varWidthPrimOps_isvalid {C : Type} (units : List (Option C))
    (k : Index) (h : 1 ≤ k.val ∧ k.val ≤ (units.length : Int)) :
    (basic.varWidthPrimOps (C := C)).isvalid units k =
      .ok (units.getD (k.val.toNat - 1) none).isSome := by
  rcases h with ⟨hk1, hk2⟩
  simp [basic.varWidthPrimOps, hk1, hk2]

private theorem getD_none_cons_drop {C : Type} :
    ∀ (units : List (Option C)) (m : Nat),
      m < units.length →
      units.getD m none :: units.drop (m + 1) = units.drop m
  | [], _, hm => by cases hm
  | _ :: _, 0, _ => rfl
  | _ :: us, m + 1, hm =>
      getD_none_cons_drop us m (Nat.lt_of_succ_lt_succ hm)

private theorem drop_filterMap_of_isSome_false {C : Type}
    (units : List (Option C)) (m : Nat) (hm : m < units.length)
    (hfalse : (units.getD m none).isSome = false) :
    (units.drop m).filterMap id = (units.drop (m + 1)).filterMap id := by
  rw [← getD_none_cons_drop units m hm]
  cases h : units.getD m none with
  | none => rfl
  | some _ =>
      rw [h] at hfalse
      cases hfalse

private theorem drop_filterMap_length_of_isSome_true {C : Type}
    (units : List (Option C)) (m : Nat) (hm : m < units.length)
    (htrue : (units.getD m none).isSome = true) :
    ((units.drop m).filterMap id).length = ((units.drop (m + 1)).filterMap id).length + 1 := by
  rw [← getD_none_cons_drop units m hm]
  cases h : units.getD m none with
  | none =>
      rw [h] at htrue
      cases htrue
  | some _ => simp [List.filterMap]

private theorem take_length_left {C : Type} :
    ∀ (A B : List C), (A ++ B).take A.length = A
  | [], _ => rfl
  | a :: as, B => congrArg (a :: ·) (take_length_left as B)

private theorem drop_length_left {C : Type} :
    ∀ (A B : List C), (A ++ B).drop A.length = B
  | [], _ => rfl
  | _ :: as, B => drop_length_left as B

private theorem filterMap_append_id {C : Type} :
    ∀ (A B : List (Option C)),
      (A ++ B).filterMap id = A.filterMap id ++ B.filterMap id
  | [], _ => rfl
  | none :: as, B => filterMap_append_id as B
  | some c :: as, B => congrArg (c :: ·) (filterMap_append_id as B)

private theorem filterMap_take_drop_split {C : Type} (units : List (Option C)) (m : Nat) :
    (units.take m).filterMap id ++ (units.drop m).filterMap id = units.filterMap id := by
  rw [← filterMap_append_id, List.take_append_drop]

private theorem filterMap_drop_length_le {C : Type} (units : List (Option C)) (m : Nat) :
    ((units.drop m).filterMap id).length ≤ (units.filterMap id).length := by
  have hsplit := filterMap_take_drop_split units m
  have hlen : ((units.take m).filterMap id).length + ((units.drop m).filterMap id).length =
      (units.filterMap id).length := by
    rw [← List.length_append, hsplit]
  omega

private theorem filterMap_take_eq {C : Type} (units : List (Option C)) (m : Nat) :
    (units.take m).filterMap id =
      (units.filterMap id).take
        ((units.filterMap id).length - ((units.drop m).filterMap id).length) := by
  have hsplit := filterMap_take_drop_split units m
  have hlen : ((units.take m).filterMap id).length + ((units.drop m).filterMap id).length =
      (units.filterMap id).length := by
    rw [← List.length_append, hsplit]
  have hsub : (units.filterMap id).length - ((units.drop m).filterMap id).length =
      ((units.take m).filterMap id).length := by omega
  rw [hsub, ← hsplit, take_length_left]

private theorem filterMap_drop_eq {C : Type} (units : List (Option C)) (m : Nat) :
    (units.drop m).filterMap id =
      (units.filterMap id).drop
        ((units.filterMap id).length - ((units.drop m).filterMap id).length) := by
  have hsplit := filterMap_take_drop_split units m
  have hlen : ((units.take m).filterMap id).length + ((units.drop m).filterMap id).length =
      (units.filterMap id).length := by
    rw [← List.length_append, hsplit]
  have hsub : (units.filterMap id).length - ((units.drop m).filterMap id).length =
      ((units.take m).filterMap id).length := by omega
  rw [hsub, ← hsplit, drop_length_left]

private theorem drop_drop_eq {α : Type} :
    ∀ (xs : List α) (a b : Nat), (xs.drop a).drop b = xs.drop (a + b)
  | xs, 0, b => by simp
  | [], _ + 1, _ => by simp
  | _ :: xs, a + 1, b => by
      rw [Nat.succ_add]
      exact drop_drop_eq xs a b

private theorem filterMap_drop_take_of_drop_nil {C : Type}
    (units : List (Option C)) (m₁ m₂ : Nat) (hle : m₁ ≤ m₂)
    (hnil : (units.drop m₂).filterMap id = []) :
    ((units.drop m₁).take (m₂ - m₁)).filterMap id = (units.drop m₁).filterMap id := by
  have hsplit := filterMap_take_drop_split (units.drop m₁) (m₂ - m₁)
  rw [drop_drop_eq, Nat.add_sub_of_le hle, hnil, List.append_nil] at hsplit
  exact hsplit

private theorem filterMap_drop_nil_of_le {C : Type}
    (units : List (Option C)) (m₁ m₂ : Nat) (hle : m₁ ≤ m₂)
    (hnil : (units.drop m₁).filterMap id = []) :
    (units.drop m₂).filterMap id = [] := by
  have hsplit := filterMap_take_drop_split (units.drop m₁) (m₂ - m₁)
  rw [drop_drop_eq, Nat.add_sub_of_le hle, hnil] at hsplit
  have hlen : (((units.drop m₁).take (m₂ - m₁)).filterMap id).length +
      ((units.drop m₂).filterMap id).length = 0 := by
    rw [← List.length_append, hsplit]
    rfl
  exact List.eq_nil_of_length_eq_zero (by omega)

private theorem lt_of_drop_nil_of_isSome_true {C : Type}
    (units : List (Option C)) (lastJ m : Nat) (hm : m < units.length)
    (hnil : (units.drop (lastJ + 1)).filterMap id = [])
    (hsome : (units.getD m none).isSome = true) :
    m < lastJ + 1 := by
  by_cases hlt : m < lastJ + 1
  · exact hlt
  · have hle : lastJ + 1 ≤ m := by omega
    have hnil_m := filterMap_drop_nil_of_le units (lastJ + 1) m hle hnil
    have hlen := drop_filterMap_length_of_isSome_true units m hm hsome
    rw [hnil_m] at hlen
    cases hlen

private theorem int_sub_zero (a : Index) :
    a - basic.int 0 = a := by
  apply Subtype.ext
  change wrapInt .i64 (a.val - 0) = a.val
  rw [Int.sub_zero]
  exact wrapInt_of_inRange .i64 a.val a.property

private theorem int_sub_boolInt_false (a : Index) :
    a - basic.boolInt false = a :=
  int_sub_zero a

private theorem int_add_zero (a : Index) :
    a + basic.int 0 = a := by
  apply Subtype.ext
  change wrapInt .i64 (a.val + 0) = a.val
  rw [Int.add_zero]
  exact wrapInt_of_inRange .i64 a.val a.property

private theorem codeunitSliceChars_from_one_idx {C : Type}
    (units : List (Option C)) (i : Index) (h1 : 1 ≤ i.val) :
    basic.codeunitSliceChars units (basic.int 1) i =
      (units.take i.val.toNat).filterMap id := by
  have hle : (basic.int 1).val ≤ i.val := h1
  have hdrop : ((basic.int 1).val - 1).toNat = 0 := rfl
  have htake : (i.val - (basic.int 1).val + 1).toNat = i.val.toNat := by
    have : (basic.int 1).val = 1 := rfl
    omega
  unfold basic.codeunitSliceChars
  simp only [hle, ↓reduceIte, hdrop, List.drop, htake]

private theorem codeunitSliceChars_to_lastIdx {C : Type}
    (units : List (Option C)) (first lastIdx : Index)
    (h1 : 1 ≤ first.val) (hle : first.val ≤ lastIdx.val)
    (hnil : (units.drop lastIdx.val.toNat).filterMap id = []) :
    basic.codeunitSliceChars units first lastIdx =
      (units.drop (first.val - 1).toNat).filterMap id := by
  have htake : (lastIdx.val - first.val + 1).toNat =
      lastIdx.val.toNat - (first.val - 1).toNat := by omega
  unfold basic.codeunitSliceChars
  simp only [hle, ↓reduceIte, htake]
  exact filterMap_drop_take_of_drop_nil units (first.val - 1).toNat lastIdx.val.toNat
    (by omega) hnil

private theorem codeunitSliceChars_gt {C : Type}
    (units : List (Option C)) (a b : Index) (hgt : b.val < a.val) :
    basic.codeunitSliceChars units a b = [] := by
  have hnot : ¬ (a.val ≤ b.val) := by omega
  simp [basic.codeunitSliceChars, hnot]

private theorem thisindInt_of_isvalid_true {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) (i : Index)
    (hi1 : 1 ≤ i.val) (hile : i.val ≤ (ops.ncodeunits s).val)
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hval : ops.isvalid s i = .ok true) :
    basic.thisindInt ops s i = .ok i := by
  have hz := add_one_val (ops.ncodeunits s) hmax
  have hne : (i.val == (ops.ncodeunits s + basic.int 1).val) = false := by
    rw [hz, beq_eq_false_iff_ne]
    omega
  have hin : (decide (0 ≤ i.val) &&
      decide (i.val ≤ (ops.ncodeunits s + basic.int 1).val)) = true := by
    rw [hz]
    simp [show 0 ≤ i.val by omega, show i.val ≤ (ops.ncodeunits s).val + 1 by omega]
  by_cases hgt1 : 1 < i.val
  · simp [basic.thisindInt, hne, hin, basic.thisindLoop, hgt1, hval]
  · simp [basic.thisindInt, hne, hin, basic.thisindLoop, hgt1]

private theorem thisindLoop_varWidth {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError) (s : S) (units : List (Option C))
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome) :
    ∀ (fuel : Nat) (i : Index),
      1 ≤ i.val →
      i.val ≤ (units.length : Int) →
      i.val - 1 ≤ (fuel : Int) →
      ∃ j : Index,
        1 ≤ j.val ∧
        j.val ≤ i.val ∧
        basic.thisindLoop ops s fuel i = .ok j ∧
        (units.drop j.val.toNat).filterMap id = (units.drop i.val.toNat).filterMap id ∧
        (j.val = 1 ∨ (units.getD (j.val.toNat - 1) none).isSome = true) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i hi1 _ hfuel
      exact ⟨i, hi1, Int.le_refl _, rfl, rfl, .inl (by omega)⟩
  | succ fuel ih =>
      intro i hi1 hile hfuel
      unfold basic.thisindLoop
      by_cases hgt1 : 1 < i.val
      · have hi_b := index_bounds i
        have hval : ops.isvalid s i = .ok (units.getD (i.val.toNat - 1) none).isSome :=
          hvalid i ⟨hi1, hile⟩
        cases hsome : (units.getD (i.val.toNat - 1) none).isSome with
        | true =>
            refine ⟨i, hi1, Int.le_refl _, ?_, rfl, .inr hsome⟩
            simp only [hgt1, ↓reduceIte, hval, bind_except_ok, hsome, pure_except]
        | false =>
            have hi'_val : (i - basic.int 1).val = i.val - 1 := by
              change wrapInt .i64 (i.val - 1) = i.val - 1
              exact wrapInt_i64_of_bounds (i.val - 1) ⟨by omega, by omega⟩
            have hfuel' : (i - basic.int 1).val - 1 ≤ (fuel : Int) := by
              have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
              omega
            obtain ⟨j, hj1, hjle, hrec, hdrop, hjok⟩ :=
              ih (i - basic.int 1) (by omega) (by omega) hfuel'
            have hstep := drop_filterMap_of_isSome_false units (i.val.toNat - 1) (by omega) hsome
            have hidx1 : (i - basic.int 1).val.toNat = i.val.toNat - 1 := by omega
            have hidx2 : i.val.toNat - 1 + 1 = i.val.toNat := by omega
            rw [hidx2, ← hidx1] at hstep
            refine ⟨j, hj1, by omega, ?_, hdrop.trans hstep, hjok⟩
            simp only [hgt1, ↓reduceIte, hval, bind_except_ok, hsome, Bool.false_eq_true, hrec]
      · refine ⟨i, hi1, Int.le_refl _, ?_, rfl, .inl (by omega)⟩
        simp [hgt1]

private theorem lastindex_varWidth_pos {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError) (intString : Index → String)
    (s : S) (units : List (Option C))
    (hpos : 1 ≤ (ops.ncodeunits s).val)
    (hnc_val : (ops.ncodeunits s).val = (units.length : Int))
    (hmax : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome) :
    ∃ lastIdx : Index,
      1 ≤ lastIdx.val ∧
      lastIdx.val ≤ (units.length : Int) ∧
      (basic.modelStringOps ops intString).lastindex s = .ok lastIdx ∧
      (units.drop lastIdx.val.toNat).filterMap id = [] ∧
      (lastIdx.val = 1 ∨ (units.getD (lastIdx.val.toNat - 1) none).isSome = true) := by
  have hz := add_one_val (ops.ncodeunits s) hmax
  have hne : ((ops.ncodeunits s).val == (ops.ncodeunits s + basic.int 1).val) = false := by
    rw [hz, beq_eq_false_iff_ne]
    omega
  have hin : (decide (0 ≤ (ops.ncodeunits s).val) &&
      decide ((ops.ncodeunits s).val ≤ (ops.ncodeunits s + basic.int 1).val)) = true := by
    rw [hz]
    simp [show 0 ≤ (ops.ncodeunits s).val by omega,
      show (ops.ncodeunits s).val ≤ (ops.ncodeunits s).val + 1 by omega]
  obtain ⟨lastIdx, h1, hle, hloop, hdrop, hok⟩ :=
    thisindLoop_varWidth ops s units hvalid ((ops.ncodeunits s).val.toNat + 1)
      (ops.ncodeunits s) hpos (by omega) (by omega)
  have htoNat : (ops.ncodeunits s).val.toNat = units.length := by omega
  refine ⟨lastIdx, h1, by omega, ?_, ?_, hok⟩
  · rw [modelStringOps_lastindex]
    simpa [basic.thisindInt, hne, hin] using hloop
  · rw [hdrop, htoNat, List.drop_length]
    rfl

private abbrev opMaxIndex (a b : Index) : Index :=
  JuliaLean.base.operators.max
    (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
    JuliaLean.base.operators.ifelseValue a b

private theorem maxOne_stop_varWidth {C : Type}
    (units : List (Option C)) (i n : Index)
    (hi1 : 1 ≤ i.val) (hn0 : 0 ≤ n.val)
    (hmin : -9223372036854775808 ≤ i.val - n.val)
    (hstop : ¬ (0 < n.val ∧ 1 < i.val)) :
    1 ≤ (opMaxIndex (basic.int 1) (i - n)).val ∧
    (opMaxIndex (basic.int 1) (i - n)).val ≤ i.val ∧
    ((units.drop ((opMaxIndex (basic.int 1) (i - n)).val - 1).toNat).filterMap id).length =
      min (units.filterMap id).length
        (((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat) := by
  have hi_b := index_bounds i
  have hn_b := index_bounds n
  have hsub_val : (i - n).val = i.val - n.val := by
    change wrapInt .i64 (i.val - n.val) = i.val - n.val
    exact wrapInt_i64_of_bounds (i.val - n.val) ⟨hmin, by omega⟩
  have h1_val : (basic.int 1).val = 1 := rfl
  by_cases hn_zero : n.val = 0
  · have hmax_eq : opMaxIndex (basic.int 1) (i - n) = i - n := by
      unfold opMaxIndex
      rw [operators_max_index]
      have hnotlt : ¬ ((i - n).val < (basic.int 1).val) := by omega
      simp only [hnotlt, ↓reduceIte]
    rw [hmax_eq]
    have hdrop_idx : ((i - n).val - 1).toNat = (i.val - 1).toNat := by omega
    have hn_toNat : n.val.toNat = 0 := by omega
    have hlen_le := filterMap_drop_length_le units (i.val - 1).toNat
    refine ⟨by omega, by omega, ?_⟩
    rw [hdrop_idx, hn_toNat]
    omega
  · have hi_eq : i.val = 1 := by omega
    have hlt1 : (i - n).val < (basic.int 1).val := by omega
    have hmax_eq : opMaxIndex (basic.int 1) (i - n) = basic.int 1 := by
      unfold opMaxIndex
      rw [operators_max_index]
      simp only [hlt1, ↓reduceIte]
    rw [hmax_eq]
    have hdrop0 : (i.val - 1).toNat = 0 := by omega
    have hdrop1 : ((basic.int 1).val - 1).toNat = 0 := rfl
    refine ⟨by omega, by omega, ?_⟩
    rw [hdrop0, hdrop1]
    simp

private theorem previndLoop_varWidth_maxOne {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError) (s : S) (units : List (Option C))
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome) :
    ∀ (fuel : Nat) (i n : Index),
      1 ≤ i.val →
      i.val ≤ (units.length : Int) + 1 →
      0 ≤ n.val →
      i.val - 1 ≤ (fuel : Int) →
      -9223372036854775808 ≤ i.val - n.val →
      ∃ res : Index,
        basic.previndLoop ops s fuel i n = .ok res ∧
        1 ≤ (opMaxIndex (basic.int 1) res).val ∧
        (opMaxIndex (basic.int 1) res).val ≤ i.val ∧
        ((units.drop ((opMaxIndex (basic.int 1) res).val - 1).toNat).filterMap id).length =
          min (units.filterMap id).length
            (((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i n hi1 _ hn0 hfuel hmin
      exact ⟨i - n, rfl, maxOne_stop_varWidth units i n hi1 hn0 hmin (by omega)⟩
  | succ fuel ih =>
      intro i n hi1 hile hn0 hfuel hmin
      unfold basic.previndLoop
      by_cases hcond : 0 < n.val ∧ 1 < i.val
      · have hi_b := index_bounds i
        have hn_b := index_bounds n
        have hi'_val : (i - basic.int 1).val = i.val - 1 := by
          change wrapInt .i64 (i.val - 1) = i.val - 1
          exact wrapInt_i64_of_bounds (i.val - 1) ⟨by omega, by omega⟩
        have hval_i' : ops.isvalid s (i - basic.int 1) =
            .ok (units.getD ((i - basic.int 1).val.toNat - 1) none).isSome :=
          hvalid (i - basic.int 1) ⟨by omega, by omega⟩
        have hfuel' : (i - basic.int 1).val - 1 ≤ (fuel : Int) := by
          have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
          omega
        have hidx1 : (i - basic.int 1).val.toNat - 1 = ((i - basic.int 1).val - 1).toNat := by
          omega
        have hidx2 : ((i - basic.int 1).val - 1).toNat + 1 = (i.val - 1).toNat := by omega
        cases hsome : (units.getD ((i - basic.int 1).val.toNat - 1) none).isSome with
        | true =>
            have hn'_val : (n - basic.boolInt true).val = n.val - 1 := by
              change wrapInt .i64 (n.val - 1) = n.val - 1
              exact wrapInt_i64_of_bounds (n.val - 1) ⟨by omega, by omega⟩
            obtain ⟨res, hrec, hres1, hres_le, hres_len⟩ :=
              ih (i - basic.int 1) (n - basic.boolInt true)
                (by omega) (by omega) (by omega) hfuel' (by omega)
            have hstep := drop_filterMap_length_of_isSome_true units
              ((i - basic.int 1).val.toNat - 1) (by omega) hsome
            rw [hidx1, hidx2] at hstep
            refine ⟨res, ?_, hres1, by omega, ?_⟩
            · simp only [hcond.1, hcond.2, decide_true, Bool.and_self, ↓reduceIte,
                hval_i', bind_except_ok, hsome, hrec]
            · omega
        | false =>
            have hn'_val : (n - basic.boolInt false).val = n.val := by
              rw [int_sub_boolInt_false]
            obtain ⟨res, hrec, hres1, hres_le, hres_len⟩ :=
              ih (i - basic.int 1) (n - basic.boolInt false)
                (by omega) (by omega) (by omega) hfuel' (by omega)
            have hstep := drop_filterMap_of_isSome_false units
              ((i - basic.int 1).val.toNat - 1) (by omega) hsome
            rw [hidx1, hidx2] at hstep
            have hstep_len : ((units.drop ((i - basic.int 1).val - 1).toNat).filterMap id).length =
                ((units.drop (i.val - 1).toNat).filterMap id).length :=
              congrArg List.length hstep
            refine ⟨res, ?_, hres1, by omega, ?_⟩
            · simp only [hcond.1, hcond.2, decide_true, Bool.and_self, ↓reduceIte,
                hval_i', bind_except_ok, hsome, hrec]
            · omega
      · have hcond' : (decide (0 < n.val) && decide (1 < i.val)) = false := by
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
          omega
        refine ⟨i - n, ?_, maxOne_stop_varWidth units i n hi1 hn0 hmin hcond⟩
        simp [hcond']

private theorem lastN_of_varWidth {t : IntTy} {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError)
    (intString : Index → String) (s : S) (units : List (Option C)) (n : JInt t)
    (hmax : (units.length : Int) + 1 ≤ 9223372036854775807)
    (hin : IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64)
    (hn0 : 0 ≤ n.val)
    (hmin : -9223372036854775808 ≤ (units.length : Int) + 1 - n.val)
    (hnc : ops.ncodeunits s = basic.int (units.length : Int))
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome)
    (hslice : ∀ a b : Index, ops.getindexSlice s a b = .ok (basic.codeunitSliceChars units a b)) :
    basic.lastN (basic.modelStringOps ops intString)
      (basic.previndInt (basic.modelStringOps ops intString) intString)
      (JuliaLean.base.int.convert .i64) s n =
      .ok ((units.filterMap id).drop ((units.filterMap id).length - n.val.toNat)) := by
  have hin1 : -9223372036854775808 ≤ n.val := hin.1
  have hin2 : n.val ≤ 9223372036854775807 := hin.2
  have hnc_val : (ops.ncodeunits s).val = (units.length : Int) := by
    rw [hnc]
    exact wrapInt_i64_of_bounds (units.length : Int) ⟨by omega, by omega⟩
  have hmax_ops : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807 := by omega
  have hend_val : (ops.ncodeunits s + basic.int 1).val = (units.length : Int) + 1 := by
    rw [add_one_val (ops.ncodeunits s) hmax_ops, hnc_val]
  have hn_val : (basic.int n.val).val = n.val :=
    wrapInt_i64_of_bounds n.val hin
  have hconv := convert_i64_of_inRange n hin
  have hend_drop : ((ops.ncodeunits s + basic.int 1).val - 1).toNat = units.length := by omega
  have hn_toNat : (basic.int n.val).val.toNat = n.val.toNat := by omega
  have hprev_step :
      ∃ res : Index,
        basic.previndInt (basic.modelStringOps ops intString) intString s
          (ops.ncodeunits s + basic.int 1) (basic.int n.val) = .ok res ∧
        1 ≤ (opMaxIndex (basic.int 1) res).val ∧
        (opMaxIndex (basic.int 1) res).val ≤ (units.length : Int) + 1 ∧
        ((units.drop ((opMaxIndex (basic.int 1) res).val - 1).toNat).filterMap id).length =
          min (units.filterMap id).length n.val.toNat := by
    rw [previndInt_modelStringOps]
    unfold basic.previndInt
    simp only [previndLoop_thisindOps]
    have hnotneg : ¬ ((basic.int n.val).val < 0) := by omega
    have hpos_end : 0 < (ops.ncodeunits s + basic.int 1).val := by omega
    have hle_end : (ops.ncodeunits s + basic.int 1).val ≤
        (ops.ncodeunits s + basic.int 1).val := Int.le_refl _
    by_cases hn_zero : (basic.int n.val).val = 0
    · have hmax_end : opMaxIndex (basic.int 1) (ops.ncodeunits s + basic.int 1) =
          ops.ncodeunits s + basic.int 1 := by
        unfold opMaxIndex
        rw [operators_max_index]
        have h1_val : (basic.int 1).val = 1 := rfl
        have hnotlt : ¬ ((ops.ncodeunits s + basic.int 1).val < (basic.int 1).val) := by omega
        simp only [hnotlt, ↓reduceIte]
      have hn0_nat : n.val.toNat = 0 := by omega
      refine ⟨ops.ncodeunits s + basic.int 1, ?_, ?_, ?_, ?_⟩
      · simp [hpos_end, hn_zero, basic.thisindInt]
      · rw [hmax_end]
        omega
      · rw [hmax_end]
        omega
      · rw [hmax_end, hend_drop, List.drop_length, hn0_nat]
        simp
    · obtain ⟨res, hloop, hres1, hres_le, hres_len⟩ :=
        previndLoop_varWidth_maxOne ops s units hvalid
          ((ops.ncodeunits s + basic.int 1).val.toNat - 1)
          (ops.ncodeunits s + basic.int 1) (basic.int n.val)
          (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hend_drop, List.drop_length, hn_toNat] at hres_len
      refine ⟨res, ?_, hres1, by omega, by simpa using hres_len⟩
      simp [hnotneg, hpos_end, hn_zero, hloop]
  obtain ⟨res, hprev, hres1, hres_le, hres_len⟩ := hprev_step
  unfold basic.lastN
  rw [modelStringOps_ncodeunits, hconv]
  simp only [bind_except_ok, hprev]
  by_cases hpos_u : 1 ≤ (ops.ncodeunits s).val
  · obtain ⟨lastIdx, hlast1, hlast_le, hlast, hdrop_last, _⟩ :=
      lastindex_varWidth_pos ops intString s units hpos_u hnc_val hmax_ops hvalid
    rw [hlast]
    simp only [bind_except_ok, modelStringOps_getindexSlice, hslice]
    apply congrArg (Except.ok (ε := JlError))
    by_cases hle_last : (opMaxIndex (basic.int 1) res).val ≤ lastIdx.val
    · rw [show JuliaLean.base.operators.max
          (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
          JuliaLean.base.operators.ifelseValue (basic.int 1) res =
        opMaxIndex (basic.int 1) res from rfl,
        codeunitSliceChars_to_lastIdx units (opMaxIndex (basic.int 1) res)
        lastIdx hres1 hle_last hdrop_last,
        filterMap_drop_eq units ((opMaxIndex (basic.int 1) res).val - 1).toNat, hres_len]
      congr 1
      omega
    · rw [show JuliaLean.base.operators.max
          (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
          JuliaLean.base.operators.ifelseValue (basic.int 1) res =
        opMaxIndex (basic.int 1) res from rfl,
        codeunitSliceChars_gt units (opMaxIndex (basic.int 1) res) lastIdx (by omega)]
      have hnil_s := filterMap_drop_nil_of_le units lastIdx.val.toNat
        ((opMaxIndex (basic.int 1) res).val - 1).toNat (by omega) hdrop_last
      rw [hnil_s] at hres_len
      have hmin0 : min (units.filterMap id).length n.val.toNat = 0 := hres_len.symm
      have hsub_len : (units.filterMap id).length - n.val.toNat =
          (units.filterMap id).length := by omega
      rw [hsub_len, List.drop_length]
  · have hunits_nil : units = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst hunits_nil
    have hnc0 : ops.ncodeunits s = basic.int 0 := by
      rw [hnc]
      rfl
    have hlast0 : (basic.modelStringOps ops intString).lastindex s = .ok (basic.int 0) := by
      have h1 : basic.int 0 + basic.int 1 = basic.int 1 := by decide
      rw [modelStringOps_lastindex]
      unfold basic.thisindInt
      rw [hnc0, h1]
      rfl
    rw [hlast0]
    simp only [bind_except_ok, modelStringOps_getindexSlice, hslice]
    apply congrArg (Except.ok (ε := JlError))
    have h0_val : (basic.int 0).val = 0 := rfl
    rw [show JuliaLean.base.operators.max
        (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
        JuliaLean.base.operators.ifelseValue (basic.int 1) res =
      opMaxIndex (basic.int 1) res from rfl,
      codeunitSliceChars_gt [] (opMaxIndex (basic.int 1) res) (basic.int 0) (by omega)]
    simp

def LastNProperty : Prop :=
  (∀ (t : IntTy) (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S) (n : JInt t),
    IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 →
    n.val < 0 →
      basic.lastN (basic.modelStringOps ops intString)
        (basic.previndInt (basic.modelStringOps ops intString) intString)
        (JuliaLean.base.int.convert .i64) s n =
        .error (ops.argumentError ("n cannot be negative: " ++ intString (basic.int n.val)))) ∧
  (∀ (t : IntTy) (S C CU CT : Type) (ops : StringOps S (List C) C CU CT JlError)
      (intString : Index → String) (s : S) (units : List (Option C)) (n : JInt t),
    (units.length : Int) + 1 ≤ IntTy.max .i64 →
    IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 →
    0 ≤ n.val →
    IntTy.min .i64 ≤ (units.length : Int) + 1 - n.val →
    ops.ncodeunits s = basic.int (units.length : Int) →
    (∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome) →
    (∀ a b : Index, ops.getindexSlice s a b = .ok (basic.codeunitSliceChars units a b)) →
      basic.lastN (basic.modelStringOps ops intString)
        (basic.previndInt (basic.modelStringOps ops intString) intString)
        (JuliaLean.base.int.convert .i64) s n =
        .ok ((units.filterMap id).drop ((units.filterMap id).length - n.val.toNat))) ∧
  (∀ (t : IntTy) (C : Type) (intString : Index → String)
      (units : List (Option C)) (n : JInt t),
    (units.length : Int) + 1 ≤ IntTy.max .i64 →
    IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 →
    0 ≤ n.val →
    IntTy.min .i64 ≤ (units.length : Int) + 1 - n.val →
      basic.lastN (basic.varWidthStringOps intString)
        (basic.previndInt (basic.varWidthStringOps intString) intString)
        (JuliaLean.base.int.convert .i64) units n =
        .ok ((units.filterMap id).drop ((units.filterMap id).length - n.val.toNat))) ∧
  (∀ (t : IntTy) (C : Type) (defaultChar : C) (intString : Index → String)
      (chars : List C) (n : JInt t),
    (chars.length : Int) + 1 ≤ IntTy.max .i64 →
    IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 →
    0 ≤ n.val →
    IntTy.min .i64 ≤ (chars.length : Int) + 1 - n.val →
      basic.lastN (basic.charListStringOps defaultChar intString)
        (basic.previndInt (basic.charListStringOps defaultChar intString) intString)
        (JuliaLean.base.int.convert .i64) chars n =
        .ok (chars.drop (chars.length - n.val.toNat)))

private theorem lastN_of_charSlice {t : IntTy} {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError)
    (intString : Index → String) (s : S) (chars : List C)
    (lenIdx startIdx nIdx : Index) (n : JInt t)
    (hnc : ops.ncodeunits s = lenIdx)
    (hnc_val : lenIdx.val = (chars.length : Int))
    (hn_conv : JuliaLean.base.int.convert .i64 n = .ok nIdx)
    (hn_val : nIdx.val = n.val)
    (hmax : lenIdx.val + 1 ≤ 9223372036854775807)
    (hn0 : 0 ≤ nIdx.val)
    (hmin : -9223372036854775808 ≤ (lenIdx + basic.int 1).val - nIdx.val)
    (hstart : basic.int ((lenIdx + basic.int 1).val - nIdx.val) = startIdx)
    (hstart_val : startIdx.val = (chars.length : Int) + 1 - n.val)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true)
    (hslice : ∀ a b : Index, ops.getindexSlice s a b = .ok (basic.charListSlice chars a b)) :
    basic.lastN (basic.modelStringOps ops intString)
      (basic.previndInt (basic.modelStringOps ops intString) intString)
      (JuliaLean.base.int.convert .i64) s n =
      .ok (chars.drop (chars.length - n.val.toNat)) := by
  have hnc_eq : (ops.ncodeunits s).val = lenIdx.val := congrArg Subtype.val hnc
  have h1_val : (basic.int 1).val = 1 := rfl
  have hz : (lenIdx + basic.int 1).val = lenIdx.val + 1 := add_one_val lenIdx hmax
  have h0 : 0 ≤ (ops.ncodeunits s).val := by omega
  have hmax_ops : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807 := by omega
  have hlast := lastindex_of_allValid ops intString s h0 hmax_ops hvalid
  have hprev := previndInt_of_allValid ops intString s
    (ops.ncodeunits s + basic.int 1) nIdx h0 hmax_ops hvalid
    (by rw [hnc]; omega) (Int.le_refl _) hn0 (by rw [hnc]; exact hmin)
  rw [hnc] at hlast hprev
  rw [hstart] at hprev
  unfold basic.lastN
  rw [modelStringOps_ncodeunits, hnc, hn_conv]
  simp only [bind_except_ok, hprev, hlast, modelStringOps_getindexSlice, hslice]
  apply congrArg (Except.ok (ε := JlError))
  by_cases hlt1 : startIdx.val < 1
  · have hmax1 : opMaxIndex (basic.int 1) startIdx = basic.int 1 := by
      unfold opMaxIndex
      rw [operators_max_index]
      simp [hlt1]
    have hdrop0 : chars.length - n.val.toNat = 0 := by omega
    rw [show JuliaLean.base.operators.max
        (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
        JuliaLean.base.operators.ifelseValue (basic.int 1) startIdx =
      opMaxIndex (basic.int 1) startIdx from rfl, hmax1, hdrop0, List.drop]
    unfold basic.charListSlice
    by_cases hleL : 1 ≤ lenIdx.val
    · have htake : lenIdx.val.toNat = chars.length := by omega
      simp [hleL, htake, List.take_length]
    · have hnil : chars = [] := by
        cases chars with
        | nil => rfl
        | cons _ _ => simp at hnc_val; omega
      subst hnil
      simp [hleL]
  · have hmax1 : opMaxIndex (basic.int 1) startIdx = startIdx := by
      unfold opMaxIndex
      rw [operators_max_index]
      simp [hlt1]
    rw [show JuliaLean.base.operators.max
        (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
        JuliaLean.base.operators.ifelseValue (basic.int 1) startIdx =
      opMaxIndex (basic.int 1) startIdx from rfl, hmax1]
    unfold basic.charListSlice
    by_cases hleL : startIdx.val ≤ lenIdx.val
    · have hdrop_idx : (startIdx.val - 1).toNat = chars.length - n.val.toNat := by omega
      have htake_idx : (lenIdx.val - startIdx.val + 1).toNat = n.val.toNat := by omega
      have hlen_drop : (chars.drop (chars.length - n.val.toNat)).length ≤ n.val.toNat := by
        rw [List.length_drop]
        omega
      simp [hleL, hdrop_idx, htake_idx, List.take_of_length_le hlen_drop]
    · have hn0_eq : n.val.toNat = 0 := by omega
      simp [hleL, hn0_eq, Nat.sub_zero, List.drop_length]

theorem lastN_proven : LastNProperty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t S R C CU CT ops intString s n hin hneg
    rw [basic.lastN, convert_i64_of_inRange n hin]
    have hneg' : (basic.int n.val).val < 0 := by
      change wrapInt .i64 n.val < 0
      rw [wrapInt_of_inRange .i64 n.val hin]
      exact hneg
    simp [basic.previndInt, hneg']
  · intro t S C CU CT ops intString s units n hmax hin hn0 hmin hnc hvalid hslice
    exact lastN_of_varWidth ops intString s units n hmax hin hn0 hmin hnc hvalid hslice
  · intro t C intString units n hmax hin hn0 hmin
    exact lastN_of_varWidth basic.varWidthPrimOps intString units units n
      hmax hin hn0 hmin rfl (varWidthPrimOps_isvalid units) (fun _ _ => rfl)
  · intro t C defaultChar intString chars n hmax hin hn0 hmin
    have hmax' : (chars.length : Int) + 1 ≤ 9223372036854775807 := hmax
    have hmin' : -9223372036854775808 ≤ (chars.length : Int) + 1 - n.val := hmin
    have hin1 : -9223372036854775808 ≤ n.val := hin.1
    have hin2 : n.val ≤ 9223372036854775807 := hin.2
    have hnc_val : ((basic.charListPrimOps defaultChar).ncodeunits chars).val =
        (chars.length : Int) :=
      wrapInt_i64_of_bounds (chars.length : Int) ⟨by omega, by omega⟩
    have hz : ((basic.charListPrimOps defaultChar).ncodeunits chars + basic.int 1).val =
        (chars.length : Int) + 1 := by
      rw [add_one_val ((basic.charListPrimOps defaultChar).ncodeunits chars) (by omega), hnc_val]
    have hn_val : (basic.int n.val).val = n.val :=
      wrapInt_i64_of_bounds n.val hin
    have hstart_val :
        (basic.int (((basic.charListPrimOps defaultChar).ncodeunits chars + basic.int 1).val -
          (basic.int n.val).val)).val = (chars.length : Int) + 1 - n.val := by
      rw [hz, hn_val]
      exact wrapInt_i64_of_bounds ((chars.length : Int) + 1 - n.val) ⟨hmin', by omega⟩
    exact lastN_of_charSlice (basic.charListPrimOps defaultChar) intString chars chars
      ((basic.charListPrimOps defaultChar).ncodeunits chars)
      (basic.int (((basic.charListPrimOps defaultChar).ncodeunits chars + basic.int 1).val -
        (basic.int n.val).val))
      (basic.int n.val) n rfl hnc_val (convert_i64_of_inRange n hin) hn_val
      (by omega) (by omega) (by omega) rfl hstart_val
      (charListPrimOps_isvalid defaultChar chars) (fun _ _ => rfl)

/-! ## String-index and reverse iteration (`EachStringIndex`, `Iterators.Reverse`) -/

def EachIndexProperty : Prop :=
  (∀ (S : Type), basic.eltypeEachStringIndex (EachStringIndex S) = Index) ∧
  (∀ (S : Type) (s : S),
    (basic.firstEachStringIndex (basic.keysString s) :
      basic.eltypeEachStringIndex (EachStringIndex S)) = basic.int 1) ∧
  (∀ (S R C CU CT E St : Type) (ops : StringOps S R C CU CT E)
      (ofIndex : Index → St)
      (gt : St → Index → Except E Bool)
      (nextind : S → St → Except E Index)
      (s : S) (st : St),
    (gt st (ops.ncodeunits s) = .ok true →
      basic.iterateEachStringIndex ops ofIndex gt nextind (basic.keysString s) (some st) =
        .ok none) ∧
    (∀ next : Index,
      gt st (ops.ncodeunits s) = .ok false →
      nextind s st = .ok next →
      basic.iterateEachStringIndex ops ofIndex gt nextind (basic.keysString s) (some st) =
        .ok (some (st, next)))) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S),
    ops.ncodeunits s = basic.int 0 →
      basic.iterateEachStringIndex (basic.modelStringOps ops intString)
        id (fun st n => .ok (JuliaLean.base.int.lt n st))
        (basic.nextindOne (basic.modelStringOps ops intString))
        (basic.keysString s) none = .ok none ∧
      basic.lengthEachStringIndex (basic.keysString s)
        (basic.lengthString (basic.modelStringOps ops intString)
          (basic.lengthInt (basic.modelStringOps ops intString))) = .ok (basic.int 0) ∧
      basic.lastEachStringIndex (basic.modelStringOps ops intString) (basic.keysString s) =
        .ok (basic.int 0)) ∧
  (∀ (t : IntTy) (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (ofIndex : Index → JInt t)
      (nextind : S → JInt t → Except E Index)
      (s : S) (i : JInt t),
    (ops.ncodeunits s).val < i.val →
      basic.iterateEachStringIndex ops ofIndex
        (fun st n => .ok (JuliaLean.base.int.lt n st))
        nextind (basic.keysString s) (some i) = .ok none) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S),
    1 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
      basic.iterateEachStringIndex (basic.modelStringOps ops intString)
        id (fun st n => .ok (JuliaLean.base.int.lt n st))
        (basic.nextindOne (basic.modelStringOps ops intString))
        (basic.keysString s) (some (ops.ncodeunits s)) =
        .ok (some (ops.ncodeunits s, ops.ncodeunits s + basic.int 1)) ∧
      basic.iterateEachStringIndex (basic.modelStringOps ops intString)
        id (fun st n => .ok (JuliaLean.base.int.lt n st))
        (basic.nextindOne (basic.modelStringOps ops intString))
        (basic.keysString s) (some (ops.ncodeunits s + basic.int 1)) = .ok none)

theorem eachIndex_proven : EachIndexProperty := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E St ops ofIndex gt nextind s st
    constructor
    · intro hgt
      simp [basic.iterateEachStringIndex, basic.keysString, hgt]
    · intro next hgt hnext
      simp [basic.iterateEachStringIndex, basic.keysString, hgt, hnext]
  · intro S R C CU CT E ops intString s hempty
    have h1 : basic.int 0 + basic.int 1 = basic.int 1 := by decide
    refine ⟨?_, ?_, ?_⟩
    · simp [basic.iterateEachStringIndex, basic.keysString, basic.firstindexString,
        hempty, int_lt_eq]
    · simp [basic.lengthEachStringIndex, basic.keysString, basic.lengthString,
        basic.lengthInt, hempty, h1, basic.rangeSteps, basic.lengthLoop]
    · simp [basic.lastEachStringIndex, basic.keysString, basic.thisindInt, hempty,
        h1, basic.thisindLoop]
  · intro t S R C CU CT E ops ofIndex nextind s i hgt
    simp [basic.iterateEachStringIndex, basic.keysString, int_lt_eq, hgt]
  · intro S R C CU CT E ops intString s h1 hmax
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hnotgt : ¬ ((ops.ncodeunits s).val < (ops.ncodeunits s).val) := by omega
    have hgt : (ops.ncodeunits s).val < (ops.ncodeunits s + basic.int 1).val := by omega
    constructor
    · simp [basic.iterateEachStringIndex, basic.keysString, int_lt_eq, hnotgt,
        basic.nextindOne, basic.nextindInt, show 0 ≤ (ops.ncodeunits s).val by omega,
        Int.sub_self, basic.nextindLoop]
    · simp [basic.iterateEachStringIndex, basic.keysString, int_lt_eq, hgt]

def ReverseIterateProperty : Prop :=
  (∀ (S R C CU CT E St : Type) (ops : StringOps S R C CU CT E)
      (ofIndex : Index → St)
      (lt : St → Index → Except E Bool)
      (getindex : S → St → Except E C)
      (prevind : S → St → Except E Index)
      (s : S) (st : St),
    (lt st (basic.firstindexString s) = .ok true →
      basic.reverseIterateString ops ofIndex lt getindex prevind ⟨s⟩ (some st) = .ok none ∧
      basic.reverseIterateIndices ops ofIndex lt prevind ⟨basic.keysString s⟩ (some st) = .ok none) ∧
    (∀ (c : C) (prev : Index),
      lt st (basic.firstindexString s) = .ok false →
      getindex s st = .ok c →
      prevind s st = .ok prev →
      basic.reverseIterateString ops ofIndex lt getindex prevind ⟨s⟩ (some st) =
        .ok (some (c, prev)) ∧
      basic.reverseIterateIndices ops ofIndex lt prevind ⟨basic.keysString s⟩ (some st) =
        .ok (some (st, prev)))) ∧
  (∀ (t : IntTy) (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (ofIndex : Index → JInt t)
      (getindex : S → JInt t → Except E C)
      (prevind : S → JInt t → Except E Index)
      (s : S) (i : JInt t),
    i.val < 1 →
      basic.reverseIterateString ops ofIndex
        (fun st first => .ok (JuliaLean.base.int.lt st first))
        getindex prevind ⟨s⟩ (some i) = .ok none ∧
      basic.reverseIterateIndices ops ofIndex
        (fun st first => .ok (JuliaLean.base.int.lt st first))
        prevind ⟨basic.keysString s⟩ (some i) = .ok none) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S),
    ops.ncodeunits s = basic.int 0 →
      basic.reverseIterateString (basic.modelStringOps ops intString)
        id (fun st first => .ok (JuliaLean.base.int.lt st first))
        (basic.getindexString (basic.modelStringOps ops intString))
        (basic.previndOne (basic.modelStringOps ops intString))
        ⟨s⟩ none = .ok none ∧
      basic.reverseIterateIndices (basic.modelStringOps ops intString)
        id (fun st first => .ok (JuliaLean.base.int.lt st first))
        (basic.previndOne (basic.modelStringOps ops intString))
        ⟨basic.keysString s⟩ none = .ok none) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (c : C) (next : Index),
    1 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    ops.isvalid s (basic.int 1) = .ok true →
    ops.iterateAt s (basic.int 1) = .ok (some (c, next)) →
      basic.reverseIterateString (basic.modelStringOps ops intString)
        id (fun st first => .ok (JuliaLean.base.int.lt st first))
        (basic.getindexString (basic.modelStringOps ops intString))
        (basic.previndOne (basic.modelStringOps ops intString))
        ⟨s⟩ (some (basic.int 1)) =
        .ok (some (c, basic.int 0)) ∧
      basic.reverseIterateIndices (basic.modelStringOps ops intString)
        id (fun st first => .ok (JuliaLean.base.int.lt st first))
        (basic.previndOne (basic.modelStringOps ops intString))
        ⟨basic.keysString s⟩ (some (basic.int 1)) =
        .ok (some (basic.int 1, basic.int 0)))

theorem reverseIterate_proven : ReverseIterateProperty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E St ops ofIndex lt getindex prevind s st
    constructor
    · intro hlt
      exact ⟨by simp [basic.reverseIterateString, hlt],
        by simp [basic.reverseIterateIndices, basic.keysString, hlt]⟩
    · intro c prev hlt hget hprev
      exact ⟨by simp [basic.reverseIterateString, hlt, hget, hprev],
        by simp [basic.reverseIterateIndices, basic.keysString, hlt, hprev]⟩
  · intro t S R C CU CT E ops ofIndex getindex prevind s i hlt
    constructor
    · simp [basic.reverseIterateString, basic.firstindexString, int_lt_eq, hlt]
    · simp [basic.reverseIterateIndices, basic.keysString, basic.firstindexString, int_lt_eq, hlt]
  · intro S R C CU CT E ops intString s hempty
    have h1 : basic.int 0 + basic.int 1 = basic.int 1 := by decide
    constructor
    · simp [basic.reverseIterateString, basic.firstindexString, basic.thisindInt,
        hempty, h1, basic.thisindLoop, int_lt_eq]
    · simp [basic.reverseIterateIndices, basic.keysString, basic.firstindexString,
        basic.thisindInt, hempty, h1, basic.thisindLoop, int_lt_eq]
  · intro S R C CU CT E ops intString s c next h1 hmax hvalid hiter
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hcb : basic.checkboundsScalar ops.ncodeunits (fun i => decide (1 ≤ i.val))
        (fun i n => decide (i.val ≤ n.val)) s (basic.int 1) = true := by
      simp [basic.checkboundsScalar, h1]
    have hnotlt : ¬ ((ops.ncodeunits s + basic.int 1).val < 1) := by omega
    have hsub1 : basic.int 1 - basic.int 1 = basic.int 0 := by decide
    constructor
    · simp [basic.reverseIterateString, basic.firstindexString, basic.getindexString,
        basic.getindexInteger, basic.checkbounds, basic.previndOne, basic.previndInt,
        basic.previndLoop, hcb, hvalid, hiter, hnotlt, hsub1, int_lt_eq]
    · simp [basic.reverseIterateIndices, basic.keysString, basic.firstindexString,
        basic.previndOne, basic.previndInt, basic.previndLoop, hnotlt, hsub1, int_lt_eq]
/-! ## Mapping, filtering, presentation, CodeUnits, and `_split_rest` -/

private theorem mapChars_general {C A B E X : Type}
    (f : C → A) (charOf : A → UInt32) (encode : UInt32 → List X)
    (isAbstractChar : A → Bool) (convertChar : A → Except E UInt32)
    (length : B → Index) (resize : B → JInt .u64 → Except E B)
    (unsafeString : B → UInt32 → JInt .u64 → Except E (B × JInt .u64))
    (argErr : String → E) (contents : B → List X)
    (hisChar : ∀ c, isAbstractChar (f c) = true)
    (hconv : ∀ c, convertChar (f c) = .ok (charOf (f c)))
    (hresize : ∀ b cap, ∃ b', resize b cap = .ok b' ∧ contents b' = contents b)
    (hwrite : ∀ b ch idx, ∃ b' w, unsafeString b ch idx = .ok (b', w) ∧
      contents b' = contents b ++ encode ch) :
    ∀ (steps : IterSteps C Index E) (chars : List C) (b : B) (index : JInt .u64),
      basic.collectIterSteps steps = .ok chars →
      ∃ out next,
        basic.mapChars (fun c => .ok (f c)) isAbstractChar convertChar length resize unsafeString
          argErr steps b index = .ok (out, next) ∧
        contents out =
          chars.foldl (fun acc c => acc ++ encode (charOf (f c))) (contents b) := by
  intro steps
  induction steps with
  | done =>
      intro chars b index hsteps
      have hnil : chars = [] := by
        have h' : (Except.ok [] : Except E (List C)) = .ok chars := hsteps
        exact (Except.ok.inj h').symm
      subst chars
      exact ⟨b, index, rfl, rfl⟩
  | fail err =>
      intro _ _ _ hsteps
      cases hsteps
  | yield c state next ih =>
      intro chars b index hsteps
      obtain ⟨rest, hrest, rfl⟩ := collectIterSteps_yield hsteps
      by_cases hcap : (index + JInt.lit .u64 3).val > (basic.toUInt64 (length b)).val
      · obtain ⟨b1, hb1, hc1⟩ := hresize b (basic.toUInt64 (length b * basic.int 2))
        obtain ⟨b2, w, hb2, hc2⟩ := hwrite b1 (charOf (f c)) index
        obtain ⟨out, nextIdx, hrec, hcout⟩ := ih state rest b2 (index + w) hrest
        refine ⟨out, nextIdx, ?_, ?_⟩
        · simpa [basic.mapChars, hisChar c, hcap, hb1, hconv c, hb2] using hrec
        · rw [hcout, hc2, hc1]
          rfl
      · obtain ⟨b2, w, hb2, hc2⟩ := hwrite b (charOf (f c)) index
        obtain ⟨out, nextIdx, hrec, hcout⟩ := ih state rest b2 (index + w) hrest
        refine ⟨out, nextIdx, ?_, ?_⟩
        · simpa [basic.mapChars, hisChar c, hcap, hconv c, hb2] using hrec
        · rw [hcout, hc2]
          rfl

private theorem foldl_append_singleton_eq_map {C Y : Type} (g : C → Y) :
    ∀ (chars : List C) (acc : List Y),
      chars.foldl (fun a c => a ++ [g c]) acc = acc ++ chars.map g
  | [], acc => by simp
  | c :: cs, acc => by
      simpa [List.map, List.append_assoc] using
        foldl_append_singleton_eq_map g cs (acc ++ [g c])

def MapProperty : Prop :=
  (∀ (S R C CU CT E A B O X : Type) (ops : StringOps S R C CU CT E)
      (iterate : S → IterSteps C Index E)
      (builder : StringBuilderOps B A E O)
      (f : C → A) (charOf : A → UInt32) (encode : UInt32 → List X)
      (contents : B → List X) (outContents : O → List X)
      (s : S) (chars : List C) (units : Index) (b0 : B),
    basic.collectIterSteps (iterate s) = .ok chars →
    builder.divide (basic.sizeofString ops s) (ops.codeunitSize (ops.codeunitType s)) = .ok units →
    builder.newStringVector (opMaxIndex (basic.int 4) units) = .ok b0 →
    contents b0 = [] →
    (∀ c, builder.isAbstractChar (f c) = true) →
    (∀ c, builder.convertChar (f c) = .ok (charOf (f c))) →
    (∀ b cap, ∃ b', builder.resize b cap = .ok b' ∧ contents b' = contents b) →
    (∀ b ch idx, ∃ b' w, builder.unsafeString b ch idx = .ok (b', w) ∧
      contents b' = contents b ++ encode ch) →
    (∀ b cap, builder.sizehint b cap = .ok ()) →
    (∀ b, ∃ out, builder.makeString b = .ok out ∧ outContents out = contents b) →
      ∃ out,
        basic.mapString ops iterate builder (fun c => .ok (f c)) s = .ok out ∧
        outContents out =
          chars.foldl (fun acc c => acc ++ encode (charOf (f c))) []) ∧
  (∀ (S R C CU CT E A : Type) (ops : StringOps S R C CU CT E)
      (iterate : S → IterSteps C Index E)
      (isAbstractChar : A → Bool) (convertChar : A → Except E UInt32)
      (f : C → A) (charOf : A → UInt32)
      (s : S) (chars : List C),
    basic.collectIterSteps (iterate s) = .ok chars →
    (∀ c, isAbstractChar (f c) = true) →
    (∀ c, convertChar (f c) = .ok (charOf (f c))) →
      basic.mapString ops iterate (basic.utf8StringBuilder isAbstractChar convertChar)
        (fun c => .ok (f c)) s =
        .ok (chars.foldl (fun acc c => acc ++ basic.utf8CharBytes (charOf (f c))) [],
          chars.map (fun c => charOf (f c)))) ∧
  (∀ (S R CU CT E : Type) (ops : StringOps S R UInt32 CU CT E)
      (iterate : S → IterSteps UInt32 Index E) (f : UInt32 → UInt32)
      (s : S) (chars : List UInt32),
    basic.collectIterSteps (iterate s) = .ok chars →
      basic.mapString ops iterate (basic.charListBuilder (E := E))
        (fun c => .ok (f c)) s = .ok (chars.map f)) ∧
  (∀ (s : StringData) (f : UInt32 → UInt32),
    basic.mapString basic.stringDataOps basic.stringDataIterateSteps
      (basic.charListBuilder (E := JlError)) (fun c => .ok (f c)) s =
      .ok (s.chars.map f)) ∧
  (∀ (S R C CU CT E A B O : Type) (ops : StringOps S R C CU CT E)
      (iterate : S → IterSteps C Index E) (builder : StringBuilderOps B A E O)
      (f : C → A) (s : S) (units : Index) (b0 : B)
      (c : C) (i : Index) (next : Index → IterSteps C Index E),
    builder.divide (basic.sizeofString ops s) (ops.codeunitSize (ops.codeunitType s)) = .ok units →
    builder.newStringVector (opMaxIndex (basic.int 4) units) = .ok b0 →
    iterate s = .yield c i next →
    builder.isAbstractChar (f c) = false →
      basic.mapString ops iterate builder (fun c => .ok (f c)) s =
        .error (ops.argumentError
          "map(f, s::AbstractString) requires f to return AbstractChar; try map(f, collect(s)) or a comprehension instead"))

theorem map_proven : MapProperty := by
  have hgen : ∀ (S R C CU CT E A B O X : Type) (ops : StringOps S R C CU CT E)
      (iterate : S → IterSteps C Index E)
      (builder : StringBuilderOps B A E O)
      (f : C → A) (charOf : A → UInt32) (encode : UInt32 → List X)
      (contents : B → List X) (outContents : O → List X)
      (s : S) (chars : List C) (units : Index) (b0 : B),
      basic.collectIterSteps (iterate s) = .ok chars →
      builder.divide (basic.sizeofString ops s) (ops.codeunitSize (ops.codeunitType s)) = .ok units →
      builder.newStringVector (opMaxIndex (basic.int 4) units) = .ok b0 →
      contents b0 = [] →
      (∀ c, builder.isAbstractChar (f c) = true) →
      (∀ c, builder.convertChar (f c) = .ok (charOf (f c))) →
      (∀ b cap, ∃ b', builder.resize b cap = .ok b' ∧ contents b' = contents b) →
      (∀ b ch idx, ∃ b' w, builder.unsafeString b ch idx = .ok (b', w) ∧
        contents b' = contents b ++ encode ch) →
      (∀ b cap, builder.sizehint b cap = .ok ()) →
      (∀ b, ∃ out, builder.makeString b = .ok out ∧ outContents out = contents b) →
        ∃ out,
          basic.mapString ops iterate builder (fun c => .ok (f c)) s = .ok out ∧
          outContents out =
            chars.foldl (fun acc c => acc ++ encode (charOf (f c))) [] := by
    intro S R C CU CT E A B O X ops iterate builder f charOf encode contents outContents
      s chars units b0 hsteps hdiv hnew hb0 hisChar hconv hresize hwrite hsize hmake
    obtain ⟨b1, nextIdx, hmap, hc1⟩ :=
      mapChars_general f charOf encode builder.isAbstractChar builder.convertChar
        builder.length builder.resize builder.unsafeString ops.argumentError contents
        hisChar hconv hresize hwrite (iterate s) chars b0 (JInt.lit .u64 1) hsteps
    obtain ⟨b2, hb2, hc2⟩ := hresize b1 (nextIdx - JInt.lit .u64 1)
    obtain ⟨out, hout, hcout⟩ := hmake b2
    refine ⟨out, ?_, ?_⟩
    · unfold basic.mapString
      rw [hdiv]
      simp only [bind_except_ok]
      rw [hnew]
      simp only [bind_except_ok]
      rw [hmap]
      simp only [bind_except_ok, hb2, hsize b2 (nextIdx - JInt.lit .u64 1), hout]
    · rw [hcout, hc2, hc1, hb0]
  have hcharList : ∀ (S R CU CT E : Type) (ops : StringOps S R UInt32 CU CT E)
      (iterate : S → IterSteps UInt32 Index E) (f : UInt32 → UInt32)
      (s : S) (chars : List UInt32),
      basic.collectIterSteps (iterate s) = .ok chars →
        basic.mapString ops iterate (basic.charListBuilder (E := E))
          (fun c => .ok (f c)) s = .ok (chars.map f) := by
    intro S R CU CT E ops iterate f s chars hsteps
    let units : Index := basic.int ((basic.sizeofString ops s).val.tdiv
      (ops.codeunitSize (ops.codeunitType s)).val)
    let b0 : StringBuffer := ⟨opMaxIndex (basic.int 4) units, []⟩
    obtain ⟨out, hout, hcout⟩ :=
      hgen S R UInt32 CU CT E UInt32 StringBuffer (List UInt32) UInt32 ops iterate
        (basic.charListBuilder (E := E)) f id (fun ch => [ch]) StringBuffer.chars id
        s chars units b0 hsteps rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
        (fun b cap => ⟨{ b with capacity := basic.int cap.val }, rfl, rfl⟩)
        (fun b ch _ => ⟨{ b with chars := b.chars ++ [ch] }, JInt.lit .u64 1, rfl, rfl⟩)
        (fun _ _ => rfl) (fun b => ⟨b.chars, rfl, rfl⟩)
    rw [hout, show out = id out from rfl, hcout]
    dsimp only [id]
    rw [foldl_append_singleton_eq_map f chars [], List.nil_append]
  refine ⟨hgen, ?_, hcharList, ?_, ?_⟩
  · intro S R C CU CT E A ops iterate isAbstractChar convertChar f charOf s chars hsteps hisChar hconv
    let builder := basic.utf8StringBuilder isAbstractChar convertChar
    let units : Index := basic.int ((basic.sizeofString ops s).val.tdiv
      (ops.codeunitSize (ops.codeunitType s)).val)
    let b0 : Utf8StringBuffer := ⟨opMaxIndex (basic.int 4) units, [], []⟩
    obtain ⟨b1, nextIdx, hmapBytes, hcBytes⟩ :=
      mapChars_general f charOf basic.utf8CharBytes builder.isAbstractChar builder.convertChar
        builder.length builder.resize builder.unsafeString ops.argumentError Utf8StringBuffer.bytes
        hisChar hconv
        (fun b cap => ⟨{ b with capacity := basic.int cap.val }, rfl, rfl⟩)
        (fun b ch _ =>
          let enc := basic.utf8CharBytes ch
          ⟨{ b with bytes := b.bytes ++ enc, chars := b.chars ++ [ch] },
           JInt.lit .u64 (Int.ofNat enc.length), rfl, rfl⟩)
        (iterate s) chars b0 (JInt.lit .u64 1) hsteps
    obtain ⟨b1', nextIdx', hmapChars, hcChars⟩ :=
      mapChars_general f charOf (fun ch => [ch]) builder.isAbstractChar builder.convertChar
        builder.length builder.resize builder.unsafeString ops.argumentError Utf8StringBuffer.chars
        hisChar hconv
        (fun b cap => ⟨{ b with capacity := basic.int cap.val }, rfl, rfl⟩)
        (fun b ch _ =>
          let enc := basic.utf8CharBytes ch
          ⟨{ b with bytes := b.bytes ++ enc, chars := b.chars ++ [ch] },
           JInt.lit .u64 (Int.ofNat enc.length), rfl, rfl⟩)
        (iterate s) chars b0 (JInt.lit .u64 1) hsteps
    have heq : (b1, nextIdx) = (b1', nextIdx') := by
      exact Except.ok.inj (hmapBytes.symm.trans hmapChars)
    cases heq
    have hbytes : b1.bytes =
        chars.foldl (fun acc c => acc ++ basic.utf8CharBytes (charOf (f c))) [] := by
      simpa [b0] using hcBytes
    have hchars : b1.chars = chars.map (fun c => charOf (f c)) := by
      have hc := hcChars
      change b1.chars =
        chars.foldl (fun acc c => acc ++ [charOf (f c)]) ([] : List UInt32) at hc
      rw [hc, foldl_append_singleton_eq_map (fun c => charOf (f c)) chars [], List.nil_append]
    unfold basic.mapString
    change (do
      let (out, index) ← basic.mapChars (fun c => .ok (f c))
        builder.isAbstractChar builder.convertChar builder.length builder.resize
        builder.unsafeString ops.argumentError (iterate s) b0 (JInt.lit .u64 1)
      let finalLength := index - JInt.lit .u64 1
      let out ← builder.resize out finalLength
      let _ ← builder.sizehint out finalLength
      builder.makeString out) = _
    rw [hmapBytes]
    simp [builder, basic.utf8StringBuilder, hbytes, hchars]
  · intro s f
    exact hcharList StringData StringData UInt8 Unit JlError
      basic.stringDataOps basic.stringDataIterateSteps f s s.chars
      (collectIterSteps_ofList (basic.int 1) s.chars)
  · intro S R C CU CT E A B O ops iterate builder f s units b0 c i next hdiv hnew hiter hnot
    unfold basic.mapString
    rw [hdiv]
    simp only [bind_except_ok]
    rw [hnew]
    simp only [bind_except_ok]
    rw [hiter]
    simp [basic.mapChars, hnot]
private theorem filterChars_general {C B E : Type}
    (f : C → Bool) (write : B → C → Except E B) (contents : B → List C)
    (hwrite : ∀ b c, ∃ b', write b c = .ok b' ∧ contents b' = contents b ++ [c]) :
    ∀ (steps : IterSteps C Index E) (chars : List C) (b : B),
      basic.collectIterSteps steps = .ok chars →
      ∃ out,
        basic.filterChars (fun c => .ok (f c)) write steps b = .ok out ∧
        contents out = contents b ++ chars.filter f := by
  intro steps
  induction steps with
  | done =>
      intro chars b hsteps
      have hnil : chars = [] := by
        have h' : (Except.ok [] : Except E (List C)) = .ok chars := hsteps
        exact (Except.ok.inj h').symm
      subst chars
      exact ⟨b, rfl, by simp⟩
  | fail err =>
      intro _ _ hsteps
      cases hsteps
  | yield c state next ih =>
      intro chars b hsteps
      obtain ⟨rest, hrest, rfl⟩ := collectIterSteps_yield hsteps
      cases hf : f c with
      | false =>
          obtain ⟨out, hrec, hcout⟩ := ih state rest b hrest
          refine ⟨out, ?_, ?_⟩
          · simpa [basic.filterChars, hf] using hrec
          · simpa [List.filter, hf] using hcout
      | true =>
          obtain ⟨b1, hb1, hc1⟩ := hwrite b c
          obtain ⟨out, hrec, hcout⟩ := ih state rest b1 hrest
          refine ⟨out, ?_, ?_⟩
          · simpa [basic.filterChars, hf, hb1] using hrec
          · rw [hcout, hc1, List.filter, hf, List.append_assoc]
            rfl

def FilterProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (iterate : S → IterSteps C Index E) (f : C → Bool)
      (s : S) (chars : List C),
    basic.collectIterSteps (iterate s) = .ok chars →
      basic.filterString ops iterate basic.ioBufferNew basic.ioBufferWrite
        basic.ioBufferTake (fun c => .ok (f c)) s = .ok (chars.filter f)) ∧
  (∀ (s : StringData) (f : UInt32 → Bool),
    basic.filterString basic.stringDataOps basic.stringDataIterateSteps
      basic.ioBufferNew basic.ioBufferWrite basic.ioBufferTake
      (fun c => .ok (f c)) s = .ok (s.chars.filter f)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (iterate : S → IterSteps C Index E) (f : C → Except E Bool)
      (s : S) (c : C) (i : Index) (next : Index → IterSteps C Index E) (err : E),
    iterate s = .yield c i next →
    f c = .error err →
      basic.filterString ops iterate basic.ioBufferNew basic.ioBufferWrite
        basic.ioBufferTake f s = .error err)

theorem filter_proven : FilterProperty := by
  have hio : ∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (iterate : S → IterSteps C Index E) (f : C → Bool)
      (s : S) (chars : List C),
      basic.collectIterSteps (iterate s) = .ok chars →
        basic.filterString ops iterate basic.ioBufferNew basic.ioBufferWrite
          basic.ioBufferTake (fun c => .ok (f c)) s = .ok (chars.filter f) := by
    intro S R C CU CT E ops iterate f s chars hsteps
    obtain ⟨b1, hfilt, hc1⟩ :=
      filterChars_general f basic.ioBufferWrite id
        (fun b c => ⟨b ++ [c], rfl, rfl⟩)
        (iterate s) chars ([] : List C) hsteps
    unfold basic.filterString basic.ioBufferNew basic.ioBufferTake
    simp only [bind_except_ok]
    rw [hfilt]
    have hc1' : b1 = chars.filter f := by simpa using hc1
    rw [hc1']
    rfl
  refine ⟨hio, ?_, ?_⟩
  · intro s f
    exact hio StringData StringData UInt32 UInt8 Unit JlError
      basic.stringDataOps basic.stringDataIterateSteps f s s.chars
      (collectIterSteps_ofList (basic.int 1) s.chars)
  · intro S R C CU CT E ops iterate f s c i next err hiter hferr
    unfold basic.filterString basic.ioBufferNew
    rw [hiter]
    simp [basic.filterChars, hferr]

def PresentationProperty : Prop :=
  (∀ (S R C CU CT E IO : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (typeName : S → String)
      (print : IO → List String → Except E Unit) (io : IO) (s : S),
    ((ops.ncodeunits s).val = 0 →
      basic.summary ops intString typeName print io s =
        print io ["empty", " ", typeName s]) ∧
    ((ops.ncodeunits s).val ≠ 0 →
      basic.summary ops intString typeName print io s =
        print io [intString (ops.ncodeunits s) ++ "-codeunit", " ", typeName s])) ∧
  (basic.isannotatedType .bottom = false ∧
    (∀ id : Nat,
      basic.isannotatedType (.annotatedString id) = true ∧
      basic.isannotatedType (.annotatedChar id) = true ∧
      basic.isannotatedType (.other id) = false) ∧
    (∀ (V : Type) (x : TypedValue V),
      basic.isannotatedValue x = true ↔
        (∃ id, x.typeof = .annotatedString id ∨ x.typeof = .annotatedChar id))) ∧
  (∀ (C S O E : Type)
      (annotatedString plainString :
        TypedValue (C ⊕ S) → List (TypedValue (C ⊕ S)) → Except E O)
      (s1 : TypedValue (C ⊕ S)) (ss : List (TypedValue (C ⊕ S)))
      (isNTuple : Bool),
    ((∀ x ∈ s1 :: ss, x.typeof = .bottom ∨ ∃ id, x.typeof = .other id) →
      basic.concat annotatedString plainString s1 ss isNTuple = plainString s1 ss) ∧
    ((∃ x ∈ s1 :: ss, ∃ id, x.typeof = .annotatedString id ∨ x.typeof = .annotatedChar id) →
      basic.concat annotatedString plainString s1 ss isNTuple = annotatedString s1 ss)) ∧
  (∀ (T E : Type) (construct : String → Except E T) (x : T ⊕ Unit),
    basic.oneString construct x = basic.convertString construct "")

theorem presentation_proven : PresentationProperty := by
  refine ⟨?_, ?_, ?_, fun _ _ _ _ => rfl⟩
  · intro S R C CU CT E IO ops intString typeName print io s
    constructor
    · intro hzero
      simp [basic.summary, basic.isemptyString, hzero]
    · intro hne
      simp [basic.summary, basic.isemptyString, hne]
  · refine ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
    intro V x
    cases h : x.typeof <;> simp [basic.isannotatedValue, basic.isannotatedType,
      basic.isSubtypeAnnotatedString, basic.isSubtypeAnnotatedChar, h]
  · intro C S O E annotatedString plainString s1 ss isNTuple
    constructor
    · intro hall
      have hnone : ∀ x ∈ s1 :: ss, basic.isannotatedValue x = false := by
        intro x hx
        rcases hall x hx with hbot | ⟨id, hoth⟩
        · simp [basic.isannotatedValue, basic.isannotatedType, hbot]
        · simp [basic.isannotatedValue, basic.isannotatedType,
            basic.isSubtypeAnnotatedString, basic.isSubtypeAnnotatedChar, hoth]
      have hs1 : basic.isannotatedValue s1 = false := hnone s1 (.head ss)
      have hss : ss.any basic.isannotatedValue = false := by
        rw [List.any_eq_false]
        intro x hx
        simp [hnone x (.tail s1 hx)]
      simp [basic.concat, hs1, hss]
    · intro hex
      rcases hex with ⟨x, hx, id, hkind⟩
      have hxtrue : basic.isannotatedValue x = true := by
        rcases hkind with hstr | hchr <;>
          simp [basic.isannotatedValue, basic.isannotatedType,
            basic.isSubtypeAnnotatedString, basic.isSubtypeAnnotatedChar, ‹_›]
      rcases List.mem_cons.mp hx with rfl | hmem
      · simp [basic.concat, hxtrue]
      · have hany : ss.any basic.isannotatedValue = true :=
          List.any_eq_true.mpr ⟨x, hmem, hxtrue⟩
        simp [basic.concat, hany]

def CodeUnitsProperty : Prop :=
  (basic.codeUnitsIndexStyle = .linear) ∧
  (∀ (S R C CU CT E : Type) (iface : AbstractStringInterface S E)
      (ops : StringOps S R C CU CT E) (sizeofType : Type → Index) (s : S),
    let cuType := fun x : S => (basic.codeunit iface x).toType
    let cu := basic.codeunits cuType s
    cu = basic.codeUnitsCtor cuType s ∧
    basic.codeUnitsSize ops cu = (ops.ncodeunits s, ()) ∧
    (ops.ncodeunits = basic.ncodeunits iface →
      basic.codeUnitsSize ops cu = (basic.ncodeunits iface s, ())) ∧
    (ops.codeunitSize (ops.codeunitType s) = sizeofType (cuType s) →
      basic.codeUnitsSizeof ops sizeofType cu = basic.sizeofString ops s ∧
      basic.codeUnitsSizeof ops sizeofType cu =
        (basic.codeUnitsSize ops cu).1 * basic.codeUnitsElsize (T := cuType s) sizeofType)) ∧
  (∀ (S R C CU E : Type) (iface : AbstractStringInterface S E)
      (ops : StringOps S R C CU CodeunitTag E) (sizeofType : Type → Index) (s : S),
    let cuType := fun x : S => (basic.codeunit iface x).toType
    let cu := basic.codeunits cuType s
    ops.ncodeunits = basic.ncodeunits iface →
    sizeofType (cuType s) = (basic.codeunit iface s).byteSize →
    0 ≤ (basic.ncodeunits iface s).val →
    4 * (basic.ncodeunits iface s).val ≤ IntTy.max .i64 →
      (basic.codeUnitsSize ops cu).1 = basic.ncodeunits iface s ∧
      (basic.codeUnitsSizeof ops sizeofType cu).val =
        (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val ∧
      (1 ≤ (basic.ncodeunits iface s).val →
        1 ≤ (basic.codeUnitsSizeof ops sizeofType cu).val ∧
        (basic.ncodeunits iface s).val ≤ (basic.codeUnitsSizeof ops sizeofType cu).val)) ∧
  (∀ (S I Out : Type) (codeunitType : S → Type) (checkboundsBool : S → I → Out)
      (s : S) (i : I),
    basic.codeUnitsCheckbounds checkboundsBool (basic.codeunits codeunitType s) i =
      checkboundsBool s i) ∧
  (∀ (t : IntTy) (S R C CU CT E : Type) (iface : AbstractStringInterface S E)
      (ops : StringOps S R C CU CT E) (s : S) (i : JInt t),
    let cuType := fun x : S => (basic.codeunit iface x).toType
    let cu := basic.codeunits cuType s
    basic.codeUnitsCheckbounds
      (fun s (i : JInt t) => basic.checkboundsScalar ops.ncodeunits
        (JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1))
        (fun i n => JuliaLean.base.int.le i n) s i) cu i = true ↔
      (1 ≤ i.val ∧ i.val ≤ (basic.codeUnitsSize ops cu).1.val)) ∧
  (∀ (S R C CU CT E : Type) (iface : AbstractStringInterface S E)
      (ops : StringOps S R C CU CT E) (intString : Index → String) (s : S) (i : Index),
    let cuType := fun x : S => (basic.codeunit iface x).toType
    let cu := basic.codeunits cuType s
    (basic.codeUnitsCheckbounds (basic.modelStringOps ops intString).checkboundsBool cu i = .ok true ↔
      (1 ≤ i.val ∧ i.val ≤ (basic.codeUnitsSize (basic.modelStringOps ops intString) cu).1.val)) ∧
    basic.codeUnitsGetindex (basic.modelStringOps ops intString) cu i = ops.codeunit s i) ∧
  (∀ (t : IntTy) (s : StringData) (i : JInt t),
    t ≠ .i64 →
    IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 →
      let cuType := fun x : StringData => (basic.codeunit basic.stringDataInterface x).toType
      let cu := basic.codeunits cuType s
      basic.codeunit basic.stringDataInterface s = .uint8 ∧
      basic.ncodeunits basic.stringDataInterface cu.s =
        (basic.codeUnitsSize basic.stringDataOps cu).1 ∧
      (basic.codeUnitsGetindex basic.stringDataOps cu (basic.int i.val)).mapError
        MethodCallError.base =
        basic.codeunitInteger basic.stringDataOps basic.isaInt
          (JuliaLean.base.int.convert .i64) s i)

theorem codeUnits_proven : CodeUnitsProperty := by
  refine ⟨rfl, ?_, ?_, fun _ _ _ _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro S R C CU CT E _ ops sizeofType s
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro hnc
      simp [basic.codeUnitsSize, basic.codeunits, basic.codeUnitsCtor, hnc]
    · intro hT
      simp [basic.codeUnitsSizeof, basic.codeunits, basic.codeUnitsCtor,
        basic.sizeofString, basic.codeUnitsSize, basic.codeUnitsElsize, hT]
  · intro S R C CU E iface ops sizeofType s cuType cu hnc hsz_eq h0 hmax4
    have hmax4' : 4 * (basic.ncodeunits iface s).val ≤ 9223372036854775807 := hmax4
    have hsz : 1 ≤ ((basic.codeunit iface s).byteSize).val ∧
        ((basic.codeunit iface s).byteSize).val ≤ 4 := by
      cases basic.codeunit iface s <;> decide
    have hprod_le : (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val ≤
        4 * (basic.ncodeunits iface s).val := by
      have := Int.mul_le_mul_of_nonneg_left hsz.2 h0
      omega
    have hprod_ge : (basic.ncodeunits iface s).val ≤
        (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val := by
      have := Int.mul_le_mul_of_nonneg_left hsz.1 h0
      omega
    have hval : (basic.codeUnitsSizeof ops sizeofType cu).val =
        (basic.ncodeunits iface s).val * ((basic.codeunit iface s).byteSize).val := by
      dsimp only [cu, cuType]
      unfold basic.codeUnitsSizeof basic.codeunits basic.codeUnitsCtor
      rw [hnc, hsz_eq]
      change wrapInt .i64 ((basic.ncodeunits iface s).val *
        ((basic.codeunit iface s).byteSize).val) = _
      exact wrapInt_i64_of_bounds _ ⟨by omega, by omega⟩
    refine ⟨by simp [cu, cuType, basic.codeUnitsSize, basic.codeunits, basic.codeUnitsCtor, hnc],
      hval, fun h1 => ⟨by omega, by omega⟩⟩
  · intro t S R C CU CT E _ ops s i
    simp [basic.codeUnitsCheckbounds, basic.codeunits, basic.codeUnitsCtor,
      basic.checkboundsScalar, basic.codeUnitsSize, int_le_one_eq, int_le_ncodeunits_eq]
  · intro S R C CU CT E _ ops intString s i
    refine ⟨?_, rfl⟩
    simp [basic.codeUnitsCheckbounds, basic.codeunits, basic.codeUnitsCtor,
      basic.checkboundsScalar, basic.codeUnitsSize]
  · intro t s i hne hin
    dsimp only
    have hisa : basic.isaInt i = false := by
      simp [basic.isaInt, beq_eq_false_iff_ne, hne]
    have hconv := convert_i64_of_inRange i hin
    refine ⟨rfl, rfl, ?_⟩
    cases hcu : basic.stringDataOps.codeunit s (basic.int i.val) <;>
      simp [basic.codeUnitsGetindex, basic.codeunits, basic.codeUnitsCtor,
        basic.codeunitInteger, hisa, hconv, hcu, Except.mapError]
private theorem inbounds_stop_varWidth {C : Type}
    (units : List (Option C)) (i n : Index)
    (hi1 : 1 ≤ i.val) (hn0 : 0 ≤ n.val)
    (hstop : ¬ (0 < n.val ∧ 1 < i.val))
    (hlen_le : ((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat ≤
      (units.filterMap id).length)
    (hok : 0 < n.val ∨ (i.val ≤ (units.length : Int) ∧
      (units.getD (i.val.toNat - 1) none).isSome = true)) :
    i - n = i ∧
    1 ≤ i.val ∧
    i.val ≤ i.val ∧
    i.val ≤ (units.length : Int) ∧
    (units.getD (i.val.toNat - 1) none).isSome = true ∧
    ((units.drop (i.val - 1).toNat).filterMap id).length =
      ((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat := by
  have hi_b := index_bounds i
  by_cases hn_zero : n.val = 0
  · have hsub : i - n = i := by
      apply Subtype.ext
      change wrapInt .i64 (i.val - n.val) = i.val
      rw [hn_zero, Int.sub_zero]
      exact wrapInt_of_inRange .i64 i.val i.property
    rcases hok with hpos | ⟨hile, hsome⟩
    · omega
    · refine ⟨hsub, hi1, Int.le_refl _, hile, hsome, by omega⟩
  · have hi_eq : i.val = 1 := by omega
    have hdrop0 : (i.val - 1).toNat = 0 := by omega
    rw [hdrop0] at hlen_le
    simp at hlen_le
    omega

private theorem previndLoop_varWidth_inbounds {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError) (s : S) (units : List (Option C))
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome) :
    ∀ (fuel : Nat) (i n : Index),
      1 ≤ i.val →
      i.val ≤ (units.length : Int) + 1 →
      0 ≤ n.val →
      i.val - 1 ≤ (fuel : Int) →
      ((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat ≤
        (units.filterMap id).length →
      (0 < n.val ∨ (i.val ≤ (units.length : Int) ∧
        (units.getD (i.val.toNat - 1) none).isSome = true)) →
      ∃ res : Index,
        basic.previndLoop ops s fuel i n = .ok res ∧
        1 ≤ res.val ∧
        res.val ≤ i.val ∧
        res.val ≤ (units.length : Int) ∧
        (units.getD (res.val.toNat - 1) none).isSome = true ∧
        ((units.drop (res.val - 1).toNat).filterMap id).length =
          ((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat := by
  intro fuel
  induction fuel with
  | zero =>
      intro i n hi1 _ hn0 hfuel hlen_le hok
      have ⟨hsub, h1, h2, h3, h4, h5⟩ :=
        inbounds_stop_varWidth units i n hi1 hn0 (by omega) hlen_le hok
      exact ⟨i, congrArg Except.ok hsub, h1, h2, h3, h4, h5⟩
  | succ fuel ih =>
      intro i n hi1 hile hn0 hfuel hlen_le hok
      unfold basic.previndLoop
      by_cases hcond : 0 < n.val ∧ 1 < i.val
      · have hi_b := index_bounds i
        have hn_b := index_bounds n
        have hi'_val : (i - basic.int 1).val = i.val - 1 := by
          change wrapInt .i64 (i.val - 1) = i.val - 1
          exact wrapInt_i64_of_bounds (i.val - 1) ⟨by omega, by omega⟩
        have hval_i' : ops.isvalid s (i - basic.int 1) =
            .ok (units.getD ((i - basic.int 1).val.toNat - 1) none).isSome :=
          hvalid (i - basic.int 1) ⟨by omega, by omega⟩
        have hfuel' : (i - basic.int 1).val - 1 ≤ (fuel : Int) := by
          have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
          omega
        have hidx1 : (i - basic.int 1).val.toNat - 1 = ((i - basic.int 1).val - 1).toNat := by
          omega
        have hidx2 : ((i - basic.int 1).val - 1).toNat + 1 = (i.val - 1).toNat := by omega
        cases hsome : (units.getD ((i - basic.int 1).val.toNat - 1) none).isSome with
        | true =>
            have hn'_val : (n - basic.boolInt true).val = n.val - 1 := by
              change wrapInt .i64 (n.val - 1) = n.val - 1
              exact wrapInt_i64_of_bounds (n.val - 1) ⟨by omega, by omega⟩
            have hstep := drop_filterMap_length_of_isSome_true units
              ((i - basic.int 1).val.toNat - 1) (by omega) hsome
            rw [hidx1, hidx2] at hstep
            obtain ⟨res, hrec, hres1, hres_le, hres_u, hres_some, hres_len⟩ :=
              ih (i - basic.int 1) (n - basic.boolInt true)
                (by omega) (by omega) (by omega) hfuel' (by omega)
                (.inr ⟨by omega, hsome⟩)
            refine ⟨res, ?_, hres1, by omega, hres_u, hres_some, by omega⟩
            simp only [hcond.1, hcond.2, decide_true, Bool.and_self, ↓reduceIte,
              hval_i', bind_except_ok, hsome, hrec]
        | false =>
            have hn'_val : (n - basic.boolInt false).val = n.val := by
              rw [int_sub_boolInt_false]
            have hstep := drop_filterMap_of_isSome_false units
              ((i - basic.int 1).val.toNat - 1) (by omega) hsome
            rw [hidx1, hidx2] at hstep
            have hstep_len : ((units.drop ((i - basic.int 1).val - 1).toNat).filterMap id).length =
                ((units.drop (i.val - 1).toNat).filterMap id).length :=
              congrArg List.length hstep
            obtain ⟨res, hrec, hres1, hres_le, hres_u, hres_some, hres_len⟩ :=
              ih (i - basic.int 1) (n - basic.boolInt false)
                (by omega) (by omega) (by omega) hfuel' (by omega)
                (.inl (by omega))
            refine ⟨res, ?_, hres1, by omega, hres_u, hres_some, by omega⟩
            simp only [hcond.1, hcond.2, decide_true, Bool.and_self, ↓reduceIte,
              hval_i', bind_except_ok, hsome, hrec]
      · have hcond' : (decide (0 < n.val) && decide (1 < i.val)) = false := by
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
          omega
        have ⟨hsub, h1, h2, h3, h4, h5⟩ :=
          inbounds_stop_varWidth units i n hi1 hn0 hcond hlen_le hok
        refine ⟨i, ?_, h1, h2, h3, h4, h5⟩
        simp [hcond', hsub]

def PrevindProperty : Prop :=
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (i n : Index),
    n.val < 0 →
      basic.previndInt (basic.modelStringOps ops intString) intString s i n =
        .error (ops.argumentError ("n cannot be negative: " ++ intString n))) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (i n : Index),
    0 ≤ n.val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    ¬ (0 < i.val ∧ i.val ≤ (ops.ncodeunits s).val + 1) →
      basic.previndInt (basic.modelStringOps ops intString) intString s i n =
        .error (ops.boundsError s i)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S),
    0 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
      basic.previndInt (basic.modelStringOps ops intString) intString s
        (ops.ncodeunits s + basic.int 1) (basic.int 0) =
        .ok (ops.ncodeunits s + basic.int 1)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (n : Index),
    0 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    1 ≤ n.val →
      basic.previndInt (basic.modelStringOps ops intString) intString s (basic.int 1) n =
        .ok (basic.int 1 - n) ∧
      basic.previndOne (basic.modelStringOps ops intString) s (basic.int 1) =
        .ok (basic.int 0)) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (i j : Index),
    (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    1 ≤ j.val ∧ j.val < i.val ∧ i.val ≤ (ops.ncodeunits s).val + 1 →
    ops.isvalid s j = .ok true →
    (∀ k : Index, j.val < k.val ∧ k.val < i.val → ops.isvalid s k = .ok false) →
      basic.previndOne (basic.modelStringOps ops intString) s i = .ok j ∧
      basic.previndInt (basic.modelStringOps ops intString) intString s i (basic.int 1) = .ok j) ∧
  (∀ (S C CU CT : Type) (ops : StringOps S (List C) C CU CT JlError)
      (intString : Index → String) (s : S) (units : List (Option C)) (i n : Index),
    (units.length : Int) + 1 ≤ IntTy.max .i64 →
    ops.ncodeunits s = basic.int (units.length : Int) →
    (∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome) →
    1 ≤ i.val ∧ i.val ≤ (units.length : Int) + 1 →
    1 ≤ n.val →
    ((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat ≤
      (units.filterMap id).length →
      ∃ res : Index,
        basic.previndInt (basic.modelStringOps ops intString) intString s i n = .ok res ∧
        1 ≤ res.val ∧ res.val ≤ i.val ∧ res.val ≤ (units.length : Int) ∧
        (units.getD (res.val.toNat - 1) none).isSome = true ∧
        ((units.drop (res.val - 1).toNat).filterMap id).length =
          ((units.drop (i.val - 1).toNat).filterMap id).length + n.val.toNat) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String) (s : S) (i n : Index),
    0 ≤ (ops.ncodeunits s).val → (ops.ncodeunits s).val + 1 ≤ IntTy.max .i64 →
    (∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val → ops.isvalid s k = .ok true) →
    1 ≤ i.val ∧ i.val ≤ (ops.ncodeunits s + basic.int 1).val →
    0 ≤ n.val → IntTy.min .i64 ≤ i.val - n.val →
      basic.previndInt (basic.modelStringOps ops intString) intString s i n =
        .ok (basic.int (i.val - n.val)) ∧
      basic.previndOne (basic.modelStringOps ops intString) s i =
        .ok (i - basic.int 1)) ∧
  (∀ (t : IntTy) (S R C CU CT : Type) (ops : StringOps S R C CU CT JlError)
      (intString : Index → String) (s : S) (i n : JInt t),
    IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 →
    IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 →
      basic.previndIntegerN (basic.modelStringOps ops intString)
        (JuliaLean.base.int.convert .i64) s i n =
        basic.previndInt (basic.modelStringOps ops intString) intString s
          (basic.int i.val) (basic.int n.val) ∧
      basic.previndInteger (basic.modelStringOps ops intString)
        (JuliaLean.base.int.convert .i64) s i =
        basic.previndOne (basic.modelStringOps ops intString) s (basic.int i.val))

theorem prevind_proven : PrevindProperty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S R C CU CT E ops intString s i n hneg
    simp [basic.previndInt, hneg]
  · intro S R C CU CT E ops intString s i n hn hmax hout
    have hnotneg : ¬ (n.val < 0) := by omega
    have hz := add_one_val (ops.ncodeunits s) hmax
    simp [basic.previndInt, hnotneg]
    intro hpos hle
    have hle' : i.val ≤ (ops.ncodeunits s + basic.int 1).val := of_decide_eq_true hle
    omega
  · intro S R C CU CT E ops intString s h0 hmax
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hpos : 0 < (ops.ncodeunits s + basic.int 1).val := by omega
    simp [basic.previndInt, basic.thisindInt, hpos]
  · intro S R C CU CT E ops intString s n h0 hmax hn
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hle : 1 ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    have hnotneg : ¬ (n.val < 0) := by omega
    have hne0 : ¬ (n.val = 0) := by omega
    have hsub1 : basic.int 1 - basic.int 1 = basic.int 0 := by decide
    constructor
    · simp [basic.previndInt, hnotneg, hle, hne0, basic.previndLoop]
    · simp [basic.previndOne, basic.previndInt, hle, basic.previndLoop, hsub1]
  · intro S R C CU CT E ops intString s i j hmax ⟨hj1, hji, hile⟩ hjval hinv
    have hz := add_one_val (ops.ncodeunits s) hmax
    have hstep : ∀ (fuel : Nat) (m : Index),
        j.val < m.val → m.val ≤ i.val → m.val - j.val ≤ (fuel : Int) →
        basic.previndLoop ops s fuel m (basic.int 1) = .ok j := by
      intro fuel
      induction fuel with
      | zero =>
          intro m hjm _ hfuel
          omega
      | succ fuel ih =>
          intro m hjm hmle hfuel
          unfold basic.previndLoop
          have hpos1 : 0 < (basic.int 1).val := by decide
          have hgt1 : 1 < m.val := by omega
          have hm_b := index_bounds m
          have hm'_val : (m - basic.int 1).val = m.val - 1 := by
            change wrapInt .i64 (m.val - 1) = m.val - 1
            exact wrapInt_i64_of_bounds (m.val - 1) ⟨by omega, by omega⟩
          by_cases heq : (m - basic.int 1).val = j.val
          · have hmj : m - basic.int 1 = j := Subtype.ext heq
            rw [hmj]
            have h1sub1 : basic.int 1 - basic.boolInt true = basic.int 0 := by decide
            have hsub0 : j - basic.int 0 = j := by
              apply Subtype.ext
              change wrapInt .i64 (j.val - 0) = j.val
              rw [Int.sub_zero]
              exact wrapInt_of_inRange .i64 j.val j.property
            cases fuel <;>
              simp [hpos1, hgt1, hjval, h1sub1, basic.previndLoop, hsub0]
          · have hlt : j.val < (m - basic.int 1).val := by omega
            have hval : ops.isvalid s (m - basic.int 1) = .ok false :=
              hinv (m - basic.int 1) ⟨hlt, by omega⟩
            have h1sub0 : basic.int 1 - basic.boolInt false = basic.int 1 := rfl
            have hfuel' : (m - basic.int 1).val - j.val ≤ (fuel : Int) := by
              have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
              omega
            have hrec := ih (m - basic.int 1) hlt (by omega) hfuel'
            simp [hpos1, hgt1, hval, h1sub0, hrec]
    have hloop := hstep (i.val.toNat - 1) i hji (Int.le_refl _) (by omega)
    have hi_pos : 0 < i.val := by omega
    have hi_le : i.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    have hres : basic.previndInt (basic.modelStringOps ops intString) intString s i (basic.int 1) =
        .ok j := by
      rw [previndInt_modelStringOps]
      unfold basic.previndInt
      rw [previndLoop_thisindOps]
      simp [hi_pos, hi_le, hloop]
    refine ⟨?_, hres⟩
    rw [basic.previndOne]
    change basic.previndInt _ intString s i (basic.int 1) = .ok j
    rw [← previndInt_modelStringOps]
    exact hres
  · intro S C CU CT ops intString s units i n hmax hnc hvalid ⟨hi1, hile⟩ hn1 hlen_le
    have hmax' : (units.length : Int) + 1 ≤ 9223372036854775807 := hmax
    have hnc_val : (ops.ncodeunits s).val = (units.length : Int) := by
      rw [hnc]
      exact wrapInt_i64_of_bounds (units.length : Int) ⟨by omega, by omega⟩
    have hz := add_one_val (ops.ncodeunits s) (by omega)
    have hnotneg : ¬ (n.val < 0) := by omega
    have hpos : 0 < i.val := by omega
    have hle : i.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    have hne0 : ¬ (n.val = 0) := by omega
    obtain ⟨res, hloop, hres1, hres_le, hres_u, hres_some, hres_len⟩ :=
      previndLoop_varWidth_inbounds ops s units hvalid (i.val.toNat - 1) i n
        hi1 hile (by omega) (by omega) hlen_le (.inl (by omega))
    refine ⟨res, ?_, hres1, hres_le, hres_u, hres_some, hres_len⟩
    rw [previndInt_modelStringOps]
    unfold basic.previndInt
    rw [previndLoop_thisindOps]
    simp [hnotneg, hpos, hle, hne0, hloop]
  · intro S R C CU CT E ops intString s i n h0 hmax hvalid ⟨hi1, hile⟩ hn0 hmin
    have h1 := previndInt_of_allValid ops intString s i (basic.int 1) h0 hmax hvalid hi1 hile
      (by decide) (by have := index_bounds i; change -9223372036854775808 ≤ i.val - 1; omega)
    refine ⟨previndInt_of_allValid ops intString s i n h0 hmax hvalid hi1 hile hn0 hmin, ?_⟩
    rw [basic.previndOne]
    change basic.previndInt _ intString s i (basic.int 1) = .ok (i - basic.int 1)
    rw [← previndInt_modelStringOps]
    exact h1
  · intro t S R C CU CT ops intString s i n hi hn
    rw [basic.previndIntegerN, basic.previndInteger,
      convert_i64_of_inRange i hi, convert_i64_of_inRange n hn, previndInt_modelStringOps]
    simp [basic.previndOne]
private theorem nextindLoop_zero {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (s : S) (z a : Index) :
    ∀ fuel : Nat, basic.nextindLoop ops s z fuel a (basic.int 0) = .ok a
  | 0 => congrArg Except.ok (int_add_zero a)
  | _ + 1 => by
      simp [basic.nextindLoop, int_add_zero]

def subStringOpsOfStringOps {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String) :
    JuliaLean.base.strings.substring.SubStringOps S C CT E where
  ncodeunits := ops.ncodeunits
  codeunitType := ops.codeunitType
  length := basic.lengthInt ops
  checkboundsRange := fun s i j => do
    let r : JuliaLean.base.strings.substring.IndexRange := ⟨i, j⟩
    let rangeOps : IntegerRangeOps JuliaLean.base.strings.substring.IndexRange Index E :=
      { isempty := fun r => decide (r.last.val < r.first.val)
        minimum := fun r => .ok r.first
        maximum := fun r => .ok r.last
        atLeastOne := JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 1)
        atMostN := fun i n => JuliaLean.base.int.le i n }
    if ← basic.checkboundsRange ops rangeOps s r then pure ()
    else throw (ops.boundsError s i)
  checkboundsViewRange := fun sub i _ => throw (ops.boundsError sub.string i)
  isvalid := ops.isvalid
  stringIndexError := ops.stringIndexError
  boundsError := fun s i _ => ops.boundsError s i
  viewBoundsError := fun sub i _ => ops.boundsError sub.string i
  nextind := basic.nextindOne (basic.modelStringOps ops intString)
  firstindex := basic.firstindexString
  thisindParent := basic.thisindInt (basic.modelStringOps ops intString)
  isasciiCodeunits := fun _ => .ok false
  sizeof := basic.sizeofString ops

private theorem subStringInt_of_gt {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String)
    (s : S) (i j : Index) (hgt : j.val < i.val) :
    JuliaLean.base.strings.substring.subStringInt
      (subStringOpsOfStringOps ops intString) s i j =
      .ok ⟨s, basic.int 0, basic.int 0⟩ := by
  unfold JuliaLean.base.strings.substring.subStringInt
    JuliaLean.base.strings.substring.typedSubString
  rw [if_pos hgt]
  rfl

private theorem subStringInt_of_valid {S R C CU CT E : Type}
    (ops : StringOps S R C CU CT E) (intString : Index → String)
    (s : S) (i j endNext : Index)
    (hi1 : 1 ≤ i.val) (hij : i.val ≤ j.val) (hj_nc : j.val ≤ (ops.ncodeunits s).val)
    (hvali : ops.isvalid s i = .ok true)
    (hvalj : ops.isvalid s j = .ok true)
    (hnextj : basic.nextindOne (basic.modelStringOps ops intString) s j = .ok endNext) :
    JuliaLean.base.strings.substring.subStringInt
      (subStringOpsOfStringOps ops intString) s i j =
      .ok ⟨s, i - basic.int 1, endNext - i⟩ := by
  have hnotlt : ¬ (j.val < i.val) := by omega
  have h1_lit : (JuliaLean.base.int.lit .i64 1).val = 1 := rfl
  unfold JuliaLean.base.strings.substring.subStringInt
    JuliaLean.base.strings.substring.typedSubString
    subStringOpsOfStringOps basic.checkboundsRange
  simp only [hnotlt, decide_false, Bool.false_eq_true, ↓reduceIte, bind_except_ok,
    int_le_one_eq, h1_lit, hi1, decide_true, Bool.not_true, int_le_ncodeunits_eq, hj_nc,
    pure_except, hvali, hvalj, hnextj]
  rfl

private theorem nextindLoop_after_last_varWidth {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError) (s : S) (units : List (Option C))
    (z lastIdx : Index)
    (hz : z.val = (units.length : Int))
    (hmax : (units.length : Int) + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome)
    (hlast1 : 1 ≤ lastIdx.val)
    (hdrop_last : (units.drop lastIdx.val.toNat).filterMap id = []) :
    ∀ (fuel : Nat) (i : Index),
      lastIdx.val ≤ i.val →
      i.val ≤ (units.length : Int) →
      (units.length : Int) - i.val ≤ (fuel : Int) →
      basic.nextindLoop ops s z fuel i (basic.int 1) = .ok (z + basic.int 1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i _ hile hfuel
      have heq : i = z := Subtype.ext (by omega)
      rw [heq]
      rfl
  | succ fuel ih =>
      intro i hlast_i hile hfuel
      unfold basic.nextindLoop
      have hpos1 : 0 < (basic.int 1).val := by decide
      by_cases hlt : i.val < z.val
      · have hi'_val : (i + basic.int 1).val = i.val + 1 :=
          add_one_val i (by change i.val + 1 ≤ 9223372036854775807; omega)
        have hval_i' : ops.isvalid s (i + basic.int 1) =
            .ok (units.getD ((i + basic.int 1).val.toNat - 1) none).isSome :=
          hvalid (i + basic.int 1) ⟨by omega, by omega⟩
        have hidx1 : (i + basic.int 1).val.toNat - 1 = i.val.toNat := by omega
        have hfalse : (units.getD ((i + basic.int 1).val.toNat - 1) none).isSome = false := by
          cases hsome : (units.getD ((i + basic.int 1).val.toNat - 1) none).isSome with
          | false => rfl
          | true =>
              have hsome' : (units.getD i.val.toNat none).isSome = true := by
                rwa [hidx1] at hsome
              have hnil_i := filterMap_drop_nil_of_le units lastIdx.val.toNat
                i.val.toNat (by omega) hdrop_last
              have hlen := drop_filterMap_length_of_isSome_true units i.val.toNat
                (by omega) hsome'
              rw [hnil_i] at hlen
              cases hlen
        have h1sub0 : basic.int 1 - basic.boolInt false = basic.int 1 :=
          int_sub_boolInt_false (basic.int 1)
        have hfuel' : (units.length : Int) - (i + basic.int 1).val ≤ (fuel : Int) := by
          have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
          omega
        have hrec := ih (i + basic.int 1) (by omega) (by omega) hfuel'
        simp only [hpos1, hlt, decide_true, Bool.and_self, ↓reduceIte,
          hval_i', bind_except_ok, hfalse, h1sub0, hrec]
      · have heq : i = z := Subtype.ext (by omega)
        rw [heq]
        have hltz : ¬ (z.val < z.val) := Int.lt_irrefl z.val
        simp [hltz]

private theorem nextindLoop_varWidth {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError) (s : S) (units : List (Option C))
    (z lastIdx : Index)
    (hz : z.val = (units.length : Int))
    (hmax : (units.length : Int) + 1 ≤ 9223372036854775807)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome)
    (_hlast1 : 1 ≤ lastIdx.val)
    (hlast_le : lastIdx.val ≤ (units.length : Int))
    (hdrop_last : (units.drop lastIdx.val.toNat).filterMap id = []) :
    ∀ (fuel : Nat) (i : Index),
      1 ≤ i.val →
      i.val ≤ (units.length : Int) →
      (units.length : Int) - i.val ≤ (fuel : Int) →
      ∃ nextIdx : Index,
        basic.nextindLoop ops s z fuel i (basic.int 1) = .ok nextIdx ∧
        basic.codeunitSliceChars units nextIdx lastIdx =
          (units.drop i.val.toNat).filterMap id ∧
        ((lastIdx.val < nextIdx.val ∧ (units.drop i.val.toNat).filterMap id = []) ∨
          (1 ≤ nextIdx.val ∧ nextIdx.val ≤ lastIdx.val ∧ ops.isvalid s nextIdx = .ok true)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i hi1 hile hfuel
      have hieq : i.val.toNat = units.length := by omega
      have hi_z : (i + basic.int 1).val = i.val + 1 :=
        add_one_val i (by change i.val + 1 ≤ 9223372036854775807; omega)
      have hnil : (units.drop i.val.toNat).filterMap id = [] := by
        rw [hieq, List.drop_length]
        rfl
      refine ⟨i + basic.int 1, rfl, ?_, .inl ⟨by omega, hnil⟩⟩
      rw [codeunitSliceChars_gt units (i + basic.int 1) lastIdx (by omega), hnil]
  | succ fuel ih =>
      intro i hi1 hile hfuel
      unfold basic.nextindLoop
      have hpos1 : 0 < (basic.int 1).val := by decide
      by_cases hlt : i.val < z.val
      · have hi'_val : (i + basic.int 1).val = i.val + 1 :=
          add_one_val i (by change i.val + 1 ≤ 9223372036854775807; omega)
        have hval_i' : ops.isvalid s (i + basic.int 1) =
            .ok (units.getD ((i + basic.int 1).val.toNat - 1) none).isSome :=
          hvalid (i + basic.int 1) ⟨by omega, by omega⟩
        have hidx1 : (i + basic.int 1).val.toNat - 1 = i.val.toNat := by omega
        have hidx2 : i.val.toNat + 1 = (i + basic.int 1).val.toNat := by omega
        cases hsome : (units.getD ((i + basic.int 1).val.toNat - 1) none).isSome with
        | true =>
            have h1sub1 : basic.int 1 - basic.boolInt true = basic.int 0 := by decide
            have hzero := nextindLoop_zero ops s z (i + basic.int 1) fuel
            have hsome' : (units.getD i.val.toNat none).isSome = true := by
              rwa [hidx1] at hsome
            have hlt_last : i.val.toNat < lastIdx.val.toNat := by
              by_cases hlt_l : i.val.toNat < lastIdx.val.toNat
              · exact hlt_l
              · have hnil_i := filterMap_drop_nil_of_le units lastIdx.val.toNat
                  i.val.toNat (by omega) hdrop_last
                have hlen := drop_filterMap_length_of_isSome_true units i.val.toNat
                  (by omega) hsome'
                rw [hnil_i] at hlen
                cases hlen
            have hval_true : ops.isvalid s (i + basic.int 1) = .ok true := by
              rwa [hsome] at hval_i'
            refine ⟨i + basic.int 1, ?_, ?_, .inr ⟨by omega, by omega, hval_true⟩⟩
            · simp only [hpos1, hlt, decide_true, Bool.and_self, ↓reduceIte,
                hval_i', bind_except_ok, hsome, h1sub1, hzero]
            · have hslice := codeunitSliceChars_to_lastIdx units (i + basic.int 1) lastIdx
                (by omega) (by omega) hdrop_last
              have hdrop_eq : ((i + basic.int 1).val - 1).toNat = i.val.toNat := by omega
              rwa [hdrop_eq] at hslice
        | false =>
            have h1sub0 : basic.int 1 - basic.boolInt false = basic.int 1 :=
              int_sub_boolInt_false (basic.int 1)
            have hfuel' : (units.length : Int) - (i + basic.int 1).val ≤ (fuel : Int) := by
              have : ((fuel + 1 : Nat) : Int) = (fuel : Int) + 1 := by omega
              omega
            obtain ⟨nextIdx, hrec, hslice, hcases⟩ :=
              ih (i + basic.int 1) (by omega) (by omega) hfuel'
            have hstep := drop_filterMap_of_isSome_false units
              ((i + basic.int 1).val.toNat - 1) (by omega) hsome
            rw [hidx1, hidx2] at hstep
            refine ⟨nextIdx, ?_, ?_, ?_⟩
            · simp only [hpos1, hlt, decide_true, Bool.and_self, ↓reduceIte,
                hval_i', bind_except_ok, hsome, h1sub0, hrec]
            · rw [hslice, ← hstep]
            · rcases hcases with ⟨hgt, hnil⟩ | hvalid_next
              · exact .inl ⟨hgt, hstep.trans hnil⟩
              · exact .inr hvalid_next
      · have hieq : i.val.toNat = units.length := by omega
        have hi_z : (i + basic.int 1).val = i.val + 1 :=
          add_one_val i (by change i.val + 1 ≤ 9223372036854775807; omega)
        have hnil : (units.drop i.val.toNat).filterMap id = [] := by
          rw [hieq, List.drop_length]
          rfl
        refine ⟨i + basic.int 1, ?_, ?_, .inl ⟨by omega, hnil⟩⟩
        · simp [hlt]
        · rw [codeunitSliceChars_gt units (i + basic.int 1) lastIdx (by omega), hnil]

private theorem splitRest_of_varWidth {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError)
    (intString : Index → String)
    (checkLengthSplitRest : Index → Index → Except JlError Index)
    (s : S) (units : List (Option C)) (n : Index)
    (hmax : (units.length : Int) + 1 ≤ 9223372036854775807)
    (hn0 : 0 ≤ n.val)
    (hnlt : n.val < ((units.filterMap id).length : Int))
    (hfirst : units ≠ [] → (units.getD 0 none).isSome = true)
    (hnc : ops.ncodeunits s = basic.int (units.length : Int))
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome)
    (hslice : ∀ a b : Index, ops.getindexSlice s a b = .ok (basic.codeunitSliceChars units a b)) :
    ∃ sub : JuliaLean.base.strings.substring.SubString S,
      basic.splitRest (basic.modelStringOps ops intString)
        (basic.previndInt (basic.modelStringOps ops intString) intString)
        (basic.nextindInt (basic.modelStringOps ops intString) intString)
        (basic.lengthString (basic.modelStringOps ops intString)
          (basic.lengthInt (basic.modelStringOps ops intString)))
        checkLengthSplitRest
        (JuliaLean.base.strings.substring.subStringInt (subStringOpsOfStringOps ops intString))
        s n =
        .ok ((units.filterMap id).take ((units.filterMap id).length - n.val.toNat), sub) ∧
      sub.string = s ∧
      basic.codeunitSliceChars units (sub.offset + basic.int 1) (sub.offset + sub.ncodeunits) =
        (units.filterMap id).drop ((units.filterMap id).length - n.val.toNat) := by
  have hn_b := index_bounds n
  have hne_nil : units ≠ [] := by
    rintro rfl
    simp at hnlt
    omega
  have hpos_len : 1 ≤ units.length := by
    cases units with
    | nil => exact False.elim (hne_nil rfl)
    | cons _ _ => simp
  have hnc_val : (ops.ncodeunits s).val = (units.length : Int) := by
    rw [hnc]
    exact wrapInt_i64_of_bounds (units.length : Int) ⟨by omega, by omega⟩
  have hmax_ops : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807 := by omega
  have hend_val : (ops.ncodeunits s + basic.int 1).val = (units.length : Int) + 1 := by
    rw [add_one_val (ops.ncodeunits s) hmax_ops, hnc_val]
  obtain ⟨lastIdx, hlast1, hlast_le, hlast, hdrop_last, hlast_ok⟩ :=
    lastindex_varWidth_pos ops intString s units (by omega) hnc_val hmax_ops hvalid
  have hlast_some : (units.getD (lastIdx.val.toNat - 1) none).isSome = true := by
    rcases hlast_ok with h1 | hsome
    · have h0 : lastIdx.val.toNat - 1 = 0 := by omega
      rw [h0]
      exact hfirst hne_nil
    · exact hsome
  have hval_last : ops.isvalid s lastIdx = .ok true := by
    rw [hvalid lastIdx ⟨hlast1, hlast_le⟩, hlast_some]
  have hdrop_last_len : ((units.drop (lastIdx.val - 1).toNat).filterMap id).length = 1 := by
    have hstep := drop_filterMap_length_of_isSome_true units (lastIdx.val.toNat - 1)
      (by omega) hlast_some
    have hidx1 : lastIdx.val.toNat - 1 = (lastIdx.val - 1).toNat := by omega
    have hidx2 : (lastIdx.val - 1).toNat + 1 = lastIdx.val.toNat := by omega
    rw [hidx1, hidx2, hdrop_last] at hstep
    exact hstep
  have hprev_step :
      ∃ splitIdx : Index,
        basic.previndInt (basic.modelStringOps ops intString) intString s lastIdx n =
          .ok splitIdx ∧
        1 ≤ splitIdx.val ∧
        splitIdx.val ≤ lastIdx.val ∧
        splitIdx.val ≤ (units.length : Int) ∧
        (units.getD (splitIdx.val.toNat - 1) none).isSome = true ∧
        ((units.drop (splitIdx.val - 1).toNat).filterMap id).length = 1 + n.val.toNat := by
    rw [previndInt_modelStringOps]
    unfold basic.previndInt
    simp only [previndLoop_thisindOps]
    have hnotneg : ¬ (n.val < 0) := by omega
    have hpos_last : 0 < lastIdx.val := by omega
    have hle_last : lastIdx.val ≤ (ops.ncodeunits s + basic.int 1).val := by omega
    by_cases hn_zero : n.val = 0
    · have hthis := thisindInt_of_isvalid_true ops s lastIdx hlast1 (by omega) hmax_ops hval_last
      refine ⟨lastIdx, ?_, hlast1, Int.le_refl _, hlast_le, hlast_some, by omega⟩
      simp [hpos_last, hle_last, hn_zero, hthis]
    · obtain ⟨splitIdx, hloop, hsp1, hsp_le, hsp_u, hsp_some, hsp_len⟩ :=
        previndLoop_varWidth_inbounds ops s units hvalid (lastIdx.val.toNat - 1) lastIdx n
          hlast1 (by omega) hn0 (by omega) (by omega) (.inl (by omega))
      refine ⟨splitIdx, ?_, hsp1, hsp_le, hsp_u, hsp_some, by omega⟩
      simp [hnotneg, hpos_last, hle_last, hn_zero, hloop]
  obtain ⟨splitIdx, hprev, hsp1, hsp_le, hsp_u, hsp_some, hsp_len⟩ := hprev_step
  have hsp_after_len : ((units.drop splitIdx.val.toNat).filterMap id).length = n.val.toNat := by
    have hstep := drop_filterMap_length_of_isSome_true units (splitIdx.val.toNat - 1)
      (by omega) hsp_some
    have hidx1 : splitIdx.val.toNat - 1 = (splitIdx.val - 1).toNat := by omega
    have hidx2 : (splitIdx.val - 1).toNat + 1 = splitIdx.val.toNat := by omega
    rw [hidx1, hidx2] at hstep
    omega
  have hnext_step :
      ∃ nextIdx : Index,
        basic.nextindInt (basic.modelStringOps ops intString) intString s splitIdx (basic.int 1) =
          .ok nextIdx ∧
        basic.codeunitSliceChars units nextIdx lastIdx =
          (units.drop splitIdx.val.toNat).filterMap id ∧
        ((lastIdx.val < nextIdx.val ∧ (units.drop splitIdx.val.toNat).filterMap id = []) ∨
          (1 ≤ nextIdx.val ∧ nextIdx.val ≤ lastIdx.val ∧ ops.isvalid s nextIdx = .ok true)) := by
    rw [nextindInt_modelStringOps]
    unfold basic.nextindInt
    simp only [nextindLoop_thisindOps]
    have hsp0 : 0 ≤ splitIdx.val := by omega
    have hsp_nc : splitIdx.val ≤ (ops.ncodeunits s).val := by omega
    obtain ⟨nextIdx, hloop, hslice_next, hcases⟩ :=
      nextindLoop_varWidth ops s units (ops.ncodeunits s) lastIdx hnc_val hmax hvalid
        hlast1 hlast_le hdrop_last ((ops.ncodeunits s).val - splitIdx.val).toNat splitIdx
        hsp1 hsp_u (by omega)
    refine ⟨nextIdx, ?_, hslice_next, hcases⟩
    simpa [hsp0, hsp_nc] using hloop
  obtain ⟨nextIdx, hnext, hslice_next, hcases⟩ := hnext_step
  have hfront : basic.codeunitSliceChars units (basic.int 1) splitIdx =
      (units.filterMap id).take ((units.filterMap id).length - n.val.toNat) := by
    rw [codeunitSliceChars_from_one_idx units splitIdx hsp1,
      filterMap_take_eq units splitIdx.val.toNat, hsp_after_len]
  have htail : basic.codeunitSliceChars units nextIdx lastIdx =
      (units.filterMap id).drop ((units.filterMap id).length - n.val.toNat) := by
    rw [hslice_next, filterMap_drop_eq units splitIdx.val.toNat, hsp_after_len]
  rcases hcases with ⟨hgt, _⟩ | ⟨hnext1, hnext_le, hval_next⟩
  · have hsub := subStringInt_of_gt ops intString s nextIdx lastIdx hgt
    refine ⟨⟨s, basic.int 0, basic.int 0⟩, ?_, rfl, ?_⟩
    · unfold basic.splitRest
      rw [hlast]
      simp only [bind_except_ok, pure_except, hprev, hnext, hsub,
        modelStringOps_getindexSlice, hslice, hfront]
    · rw [ ← htail, codeunitSliceChars_gt units nextIdx lastIdx hgt]
      rfl
  · have hnext_last :
        basic.nextindOne (basic.modelStringOps ops intString) s lastIdx =
          .ok (ops.ncodeunits s + basic.int 1) := by
      rw [basic.nextindOne]
      change basic.nextindInt _ intString s lastIdx (basic.int 1) =
        .ok (ops.ncodeunits s + basic.int 1)
      unfold basic.nextindInt
      simp only [nextindLoop_thisindOps]
      have hlast0 : 0 ≤ lastIdx.val := by omega
      have hlast_nc : lastIdx.val ≤ (ops.ncodeunits s).val := by omega
      have hloop := nextindLoop_after_last_varWidth ops s units (ops.ncodeunits s) lastIdx
        hnc_val hmax hvalid hlast1 hdrop_last
        ((ops.ncodeunits s).val - lastIdx.val).toNat lastIdx
        (Int.le_refl _) hlast_le (by omega)
      simpa [hlast0, hlast_nc] using hloop
    have hsub := subStringInt_of_valid ops intString s nextIdx lastIdx
      (ops.ncodeunits s + basic.int 1)
      hnext1 hnext_le (by omega) hval_next hval_last hnext_last
    have hoff1 : nextIdx - basic.int 1 + basic.int 1 = nextIdx :=
      sub_one_add_one nextIdx (by omega)
    have hoff_end : nextIdx - basic.int 1 + (ops.ncodeunits s + basic.int 1 - nextIdx) =
        ops.ncodeunits s := by
      have hnext_b := index_bounds nextIdx
      have hnc_b := index_bounds (ops.ncodeunits s)
      have hsub1 : (nextIdx - basic.int 1).val = nextIdx.val - 1 :=
        wrapInt_i64_of_bounds (nextIdx.val - 1) ⟨by omega, by omega⟩
      have hsub2 : (ops.ncodeunits s + basic.int 1 - nextIdx).val =
          (ops.ncodeunits s).val + 1 - nextIdx.val := by
        change wrapInt .i64 ((ops.ncodeunits s + basic.int 1).val - nextIdx.val) = _
        rw [add_one_val (ops.ncodeunits s) hmax_ops]
        exact wrapInt_i64_of_bounds ((ops.ncodeunits s).val + 1 - nextIdx.val) ⟨by omega, by omega⟩
      apply Subtype.ext
      change wrapInt .i64 ((nextIdx - basic.int 1).val +
        (ops.ncodeunits s + basic.int 1 - nextIdx).val) = (ops.ncodeunits s).val
      rw [hsub1, hsub2]
      have hsum : nextIdx.val - 1 + ((ops.ncodeunits s).val + 1 - nextIdx.val) =
          (ops.ncodeunits s).val := by omega
      rw [hsum]
      exact wrapInt_of_inRange .i64 (ops.ncodeunits s).val (ops.ncodeunits s).property
    have hdrop_nc : (units.drop (ops.ncodeunits s).val.toNat).filterMap id = [] := by
      have htoNat : (ops.ncodeunits s).val.toNat = units.length := by omega
      rw [htoNat, List.drop_length]
      rfl
    have hslice_nc : basic.codeunitSliceChars units nextIdx (ops.ncodeunits s) =
        basic.codeunitSliceChars units nextIdx lastIdx := by
      rw [codeunitSliceChars_to_lastIdx units nextIdx (ops.ncodeunits s)
        hnext1 (by omega) hdrop_nc,
        codeunitSliceChars_to_lastIdx units nextIdx lastIdx hnext1 hnext_le hdrop_last]
    refine ⟨⟨s, nextIdx - basic.int 1, ops.ncodeunits s + basic.int 1 - nextIdx⟩, ?_, rfl, ?_⟩
    · unfold basic.splitRest
      rw [hlast]
      simp only [bind_except_ok, pure_except, hprev, hnext, hsub,
        modelStringOps_getindexSlice, hslice, hfront]
    · rw [hoff1, hoff_end, hslice_nc, htail]

def SplitRestProperty : Prop :=
  (∀ (S C CU CT : Type) (ops : StringOps S (List C) C CU CT JlError)
      (intString : Index → String)
      (checkLengthSplitRest : Index → Index → Except JlError Index)
      (s : S) (units : List (Option C)) (n : Index),
    (units.length : Int) + 1 ≤ IntTy.max .i64 →
    0 ≤ n.val → n.val < ((units.filterMap id).length : Int) →
    (units ≠ [] → (units.getD 0 none).isSome = true) →
    ops.ncodeunits s = basic.int (units.length : Int) →
    (∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (units.length : Int) →
      ops.isvalid s k = .ok (units.getD (k.val.toNat - 1) none).isSome) →
    (∀ a b : Index, ops.getindexSlice s a b = .ok (basic.codeunitSliceChars units a b)) →
      let chars := units.filterMap id
      ∃ sub : JuliaLean.base.strings.substring.SubString S,
        basic.splitRest (basic.modelStringOps ops intString)
          (basic.previndInt (basic.modelStringOps ops intString) intString)
          (basic.nextindInt (basic.modelStringOps ops intString) intString)
          (basic.lengthString (basic.modelStringOps ops intString)
            (basic.lengthInt (basic.modelStringOps ops intString)))
          checkLengthSplitRest
          (JuliaLean.base.strings.substring.subStringInt (subStringOpsOfStringOps ops intString))
          s n =
          .ok (chars.take (chars.length - n.val.toNat), sub) ∧
        sub.string = s ∧
        basic.codeunitSliceChars units (sub.offset + basic.int 1) (sub.offset + sub.ncodeunits) =
          chars.drop (chars.length - n.val.toNat)) ∧
  (∀ (C : Type) (intString : Index → String)
      (checkLengthSplitRest : Index → Index → Except JlError Index)
      (units : List (Option C)) (n : Index),
    (units.length : Int) + 1 ≤ IntTy.max .i64 →
    0 ≤ n.val → n.val < ((units.filterMap id).length : Int) →
    (units ≠ [] → (units.getD 0 none).isSome = true) →
      let chars := units.filterMap id
      ∃ sub : JuliaLean.base.strings.substring.SubString (List (Option C)),
        basic.splitRest (basic.varWidthStringOps intString)
          (basic.previndInt (basic.varWidthStringOps intString) intString)
          (basic.nextindInt (basic.varWidthStringOps intString) intString)
          (basic.lengthString (basic.varWidthStringOps intString)
            (basic.lengthInt (basic.varWidthStringOps intString)))
          checkLengthSplitRest
          (JuliaLean.base.strings.substring.subStringInt
            (subStringOpsOfStringOps basic.varWidthPrimOps intString))
          units n =
          .ok (chars.take (chars.length - n.val.toNat), sub) ∧
        sub.string = units ∧
        basic.codeunitSliceChars units (sub.offset + basic.int 1) (sub.offset + sub.ncodeunits) =
          chars.drop (chars.length - n.val.toNat) ∧
        chars.take (chars.length - n.val.toNat) ++
          chars.drop (chars.length - n.val.toNat) = chars ∧
        (chars.drop (chars.length - n.val.toNat)).length = n.val.toNat) ∧
  (∀ (C : Type) (defaultChar : C) (intString : Index → String)
      (checkLengthSplitRest : Index → Index → Except JlError Index)
      (chars : List C) (n : Index),
    (chars.length : Int) + 1 ≤ IntTy.max .i64 →
    0 ≤ n.val → n.val < (chars.length : Int) →
      ∃ sub : JuliaLean.base.strings.substring.SubString (List C),
        basic.splitRest (basic.charListStringOps defaultChar intString)
          (basic.previndInt (basic.charListStringOps defaultChar intString) intString)
          (basic.nextindInt (basic.charListStringOps defaultChar intString) intString)
          (basic.lengthString (basic.charListStringOps defaultChar intString)
            (basic.lengthInt (basic.charListStringOps defaultChar intString)))
          checkLengthSplitRest
          (JuliaLean.base.strings.substring.subStringInt
            (subStringOpsOfStringOps (basic.charListPrimOps defaultChar) intString))
          chars n =
          .ok (chars.take (chars.length - n.val.toNat), sub) ∧
        sub.string = chars ∧
        basic.charListSlice chars (sub.offset + basic.int 1) (sub.offset + sub.ncodeunits) =
          chars.drop (chars.length - n.val.toNat) ∧
        chars.take (chars.length - n.val.toNat) ++
          chars.drop (chars.length - n.val.toNat) = chars ∧
        (chars.drop (chars.length - n.val.toNat)).length = n.val.toNat) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String)
      (prevind nextind : S → Index → Index → Except E Index)
      (length : S → Except E Index)
      (checkLengthSplitRest : Index → Index → Except E Index)
      (s : S) (n lastind : Index) (err : E),
    ops.lastindex s = .ok lastind →
    prevind s lastind n = .error err →
    ops.isBoundsError err = false →
      basic.splitRest ops prevind nextind length checkLengthSplitRest
        (JuliaLean.base.strings.substring.subStringInt (subStringOpsOfStringOps ops intString))
        s n = .error err) ∧
  (∀ (S R C CU CT E : Type) (ops : StringOps S R C CU CT E)
      (intString : Index → String)
      (prevind nextind : S → Index → Index → Except E Index)
      (length : S → Except E Index)
      (checkLengthSplitRest : Index → Index → Except E Index)
      (s : S) (n lastind len : Index) (err : E),
    ops.lastindex s = .ok lastind →
    prevind s lastind n = .error err →
    ops.isBoundsError err = true →
    length s = .ok len →
      basic.splitRest ops prevind nextind length checkLengthSplitRest
        (JuliaLean.base.strings.substring.subStringInt (subStringOpsOfStringOps ops intString))
        s n =
        (do
          let i ← checkLengthSplitRest len n
          let next ← nextind s i (basic.int 1)
          let lastN ← JuliaLean.base.strings.substring.subStringInt
            (subStringOpsOfStringOps ops intString) s next lastind
          let front ← ops.getindexSlice s (basic.int 1) i
          pure (front, lastN)))

private theorem splitRest_of_charSlice {S C CU CT : Type}
    (ops : StringOps S (List C) C CU CT JlError)
    (intString : Index → String)
    (checkLengthSplitRest : Index → Index → Except JlError Index)
    (s : S) (chars : List C) (lenIdx splitIdx n : Index)
    (hnc : ops.ncodeunits s = lenIdx)
    (hnc_val : lenIdx.val = (chars.length : Int))
    (hmax : lenIdx.val + 1 ≤ 9223372036854775807)
    (hn0 : 0 ≤ n.val) (hnlt : n.val < lenIdx.val)
    (hsplit : basic.int (lenIdx.val - n.val) = splitIdx)
    (hsplit_val : splitIdx.val = (chars.length : Int) - n.val)
    (hvalid : ∀ k : Index, 1 ≤ k.val ∧ k.val ≤ (ops.ncodeunits s).val →
      ops.isvalid s k = .ok true)
    (hslice : ∀ a b : Index, ops.getindexSlice s a b = .ok (basic.charListSlice chars a b)) :
    ∃ sub : JuliaLean.base.strings.substring.SubString S,
      basic.splitRest (basic.modelStringOps ops intString)
        (basic.previndInt (basic.modelStringOps ops intString) intString)
        (basic.nextindInt (basic.modelStringOps ops intString) intString)
        (basic.lengthString (basic.modelStringOps ops intString)
          (basic.lengthInt (basic.modelStringOps ops intString)))
        checkLengthSplitRest
        (JuliaLean.base.strings.substring.subStringInt (subStringOpsOfStringOps ops intString))
        s n =
        .ok (chars.take (chars.length - n.val.toNat), sub) ∧
      sub.string = s ∧
      basic.charListSlice chars (sub.offset + basic.int 1) (sub.offset + sub.ncodeunits) =
        chars.drop (chars.length - n.val.toNat) := by
  have hnc_eq : (ops.ncodeunits s).val = lenIdx.val := congrArg Subtype.val hnc
  have h1_val : (basic.int 1).val = 1 := rfl
  have hn_b := index_bounds n
  have hz : (ops.ncodeunits s + basic.int 1).val = lenIdx.val + 1 := by
    rw [hnc]
    exact add_one_val lenIdx hmax
  have h0 : 0 ≤ (ops.ncodeunits s).val := by omega
  have hmax_ops : (ops.ncodeunits s).val + 1 ≤ 9223372036854775807 := by omega
  have hlast := lastindex_of_allValid ops intString s h0 hmax_ops hvalid
  have hprev := previndInt_of_allValid ops intString s (ops.ncodeunits s) n
    h0 hmax_ops hvalid (by omega) (by omega) hn0 (by omega)
  rw [hnc] at hlast hprev
  rw [hsplit] at hprev
  have hnext := nextindInt_one_of_allValid ops intString s splitIdx
    hmax_ops hvalid (by omega) (by omega)
  have hfront : basic.charListSlice chars (basic.int 1) splitIdx =
      chars.take (chars.length - n.val.toNat) := by
    unfold basic.charListSlice
    have h1le : 1 ≤ splitIdx.val := by omega
    have hlen : splitIdx.val.toNat = chars.length - n.val.toNat := by omega
    simp [h1le, hlen]
  have hstep_val : (splitIdx + basic.int 1).val = (chars.length : Int) - n.val + 1 := by
    rw [add_one_val splitIdx (by change splitIdx.val + 1 ≤ 9223372036854775807; omega),
      hsplit_val]
  have htail : basic.charListSlice chars (splitIdx + basic.int 1) lenIdx =
      chars.drop (chars.length - n.val.toNat) := by
    unfold basic.charListSlice
    by_cases hleL : (splitIdx + basic.int 1).val ≤ lenIdx.val
    · have hdrop_idx : ((splitIdx + basic.int 1).val - 1).toNat =
          chars.length - n.val.toNat := by omega
      have htake_idx : (lenIdx.val - (splitIdx + basic.int 1).val + 1).toNat =
          n.val.toNat := by omega
      have hlen_drop : (chars.drop (chars.length - n.val.toNat)).length ≤ n.val.toNat := by
        rw [List.length_drop]
        omega
      simp [hleL, hdrop_idx, htake_idx, List.take_of_length_le hlen_drop]
    · have hn0_eq : n.val.toNat = 0 := by omega
      simp [hleL, hn0_eq, Nat.sub_zero, List.drop_length]
  by_cases hleL : (splitIdx + basic.int 1).val ≤ lenIdx.val
  · have hnext_last :
        basic.nextindOne (basic.modelStringOps ops intString) s lenIdx =
          .ok (lenIdx + basic.int 1) := by
      rw [basic.nextindOne]
      change basic.nextindInt _ intString s lenIdx (basic.int 1) = .ok (lenIdx + basic.int 1)
      rw [← nextindInt_modelStringOps]
      exact nextindInt_one_of_allValid ops intString s lenIdx hmax_ops hvalid
        (by omega) (by omega)
    have hsub := subStringInt_of_valid ops intString s (splitIdx + basic.int 1) lenIdx
      (lenIdx + basic.int 1)
      (by omega) hleL (by omega)
      (hvalid (splitIdx + basic.int 1) ⟨by omega, by omega⟩)
      (hvalid lenIdx ⟨by omega, by omega⟩) hnext_last
    have hoff1 : splitIdx + basic.int 1 - basic.int 1 + basic.int 1 = splitIdx + basic.int 1 :=
      sub_one_add_one (splitIdx + basic.int 1) (by omega)
    have hoff_end : splitIdx + basic.int 1 - basic.int 1 +
        (lenIdx + basic.int 1 - (splitIdx + basic.int 1)) = lenIdx := by
      have hnext_b := index_bounds (splitIdx + basic.int 1)
      have hlen_b := index_bounds lenIdx
      have hsub1 : (splitIdx + basic.int 1 - basic.int 1).val = (splitIdx + basic.int 1).val - 1 :=
        wrapInt_i64_of_bounds ((splitIdx + basic.int 1).val - 1) ⟨by omega, by omega⟩
      have hsub2 : (lenIdx + basic.int 1 - (splitIdx + basic.int 1)).val =
          lenIdx.val + 1 - (splitIdx + basic.int 1).val := by
        change wrapInt .i64 ((lenIdx + basic.int 1).val - (splitIdx + basic.int 1).val) = _
        rw [add_one_val lenIdx hmax]
        exact wrapInt_i64_of_bounds (lenIdx.val + 1 - (splitIdx + basic.int 1).val) ⟨by omega, by omega⟩
      apply Subtype.ext
      change wrapInt .i64 ((splitIdx + basic.int 1 - basic.int 1).val +
        (lenIdx + basic.int 1 - (splitIdx + basic.int 1)).val) = lenIdx.val
      rw [hsub1, hsub2]
      have hsum : (splitIdx + basic.int 1).val - 1 +
          (lenIdx.val + 1 - (splitIdx + basic.int 1).val) = lenIdx.val := by omega
      rw [hsum]
      exact wrapInt_of_inRange .i64 lenIdx.val lenIdx.property
    refine ⟨⟨s, splitIdx + basic.int 1 - basic.int 1,
        lenIdx + basic.int 1 - (splitIdx + basic.int 1)⟩, ?_, rfl, ?_⟩
    · unfold basic.splitRest
      rw [hlast]
      simp only [bind_except_ok, pure_except, hprev, hnext, hsub,
        modelStringOps_getindexSlice, hslice, hfront]
    · rw [hoff1, hoff_end, htail]
  · have hgt : lenIdx.val < (splitIdx + basic.int 1).val := by omega
    have hsub := subStringInt_of_gt ops intString s (splitIdx + basic.int 1) lenIdx hgt
    refine ⟨⟨s, basic.int 0, basic.int 0⟩, ?_, rfl, ?_⟩
    · unfold basic.splitRest
      rw [hlast]
      simp only [bind_except_ok, pure_except, hprev, hnext, hsub,
        modelStringOps_getindexSlice, hslice, hfront]
    · have h01 : basic.int 0 + basic.int 1 = basic.int 1 := by decide
      have h00 : basic.int 0 + basic.int 0 = basic.int 0 := by decide
      rw [h01, h00, ← htail]
      have hnotle0 : ¬ ((basic.int 1).val ≤ (basic.int 0).val) := by decide
      unfold basic.charListSlice
      simp [hnotle0, hleL]

theorem splitRest_proven : SplitRestProperty := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S C CU CT ops intString checkLengthSplitRest s units n hmax hn0 hnlt hfirst hnc hvalid hslice
    exact splitRest_of_varWidth ops intString checkLengthSplitRest s units n
      hmax hn0 hnlt hfirst hnc hvalid hslice
  · intro C intString checkLengthSplitRest units n hmax hn0 hnlt hfirst
    have hn_b := index_bounds n
    obtain ⟨sub, hsplit, hstr, hchars⟩ :=
      splitRest_of_varWidth basic.varWidthPrimOps intString checkLengthSplitRest
        units units n hmax hn0 hnlt hfirst rfl (varWidthPrimOps_isvalid units) (fun _ _ => rfl)
    refine ⟨sub, hsplit, hstr, hchars, List.take_append_drop _ (units.filterMap id), ?_⟩
    rw [List.length_drop]
    omega
  · intro C defaultChar intString checkLengthSplitRest chars n hmax hn0 hnlt
    have hmax' : (chars.length : Int) + 1 ≤ 9223372036854775807 := hmax
    have hn_b := index_bounds n
    have hnc_val : ((basic.charListPrimOps defaultChar).ncodeunits chars).val =
        (chars.length : Int) :=
      wrapInt_i64_of_bounds (chars.length : Int) ⟨by omega, by omega⟩
    have hsplit_val :
        (basic.int (((basic.charListPrimOps defaultChar).ncodeunits chars).val - n.val)).val =
        (chars.length : Int) - n.val := by
      rw [hnc_val]
      exact wrapInt_i64_of_bounds ((chars.length : Int) - n.val) ⟨by omega, by omega⟩
    obtain ⟨sub, hsplit, hstr, hchars⟩ :=
      splitRest_of_charSlice (basic.charListPrimOps defaultChar) intString
        checkLengthSplitRest chars chars
        ((basic.charListPrimOps defaultChar).ncodeunits chars)
        (basic.int (((basic.charListPrimOps defaultChar).ncodeunits chars).val - n.val))
        n rfl hnc_val (by omega) hn0 (by omega) rfl hsplit_val
        (charListPrimOps_isvalid defaultChar chars) (fun _ _ => rfl)
    refine ⟨sub, hsplit, hstr, hchars, List.take_append_drop _ chars, ?_⟩
    rw [List.length_drop]
    omega
  · intro S R C CU CT E ops intString prevind nextind length checkLengthSplitRest s n lastind err
      hlast hprev hnotb
    unfold basic.splitRest
    rw [hlast]
    simp only [bind_except_ok]
    rw [hprev]
    simp [hnotb]
  · intro S R C CU CT E ops intString prevind nextind length checkLengthSplitRest s n lastind len err
      hlast hprev hb hlen
    unfold basic.splitRest
    rw [hlast]
    simp only [bind_except_ok]
    rw [hprev]
    simp [hb, hlen]
def entries : List Entry := [
  { id := "strings-first-n-overflow", juliaFile := "base/strings/basic.jl"
    juliaFns := ["first(::AbstractString, ::Integer)", "nextind(::AbstractString, ::Int, ::Int)"]
    statement := "first(s, n) with n >= length(s) returns the whole string s."
    source := "base/strings/basic.jl:684-686"
    status := .refuted, prop := ``FirstNAll, thm := some ``firstNAll_refuted
    issue := "none found"
    notes := "Retains the source-confirmed overflow counterexample." },
  { id := "strings-nextind-n-overflow", juliaFile := "base/strings/basic.jl"
    juliaFns := ["nextind(::AbstractString, ::Int, ::Int)"]
    statement := "nextind(s, i, n) with n >= 1 and 0 <= i <= ncodeunits(s) returns an index greater than i."
    source := "base/strings/basic.jl:529-534"
    status := .refuted, prop := ``NextindNIncreasing, thm := some ``nextindNIncreasing_refuted
    issue := "none found"
    notes := "Retains the source-confirmed wrapping counterexample." },
  { id := "stringscova-basic-convert-faithful", juliaFile := "base/strings/basic.jl"
    juliaFns := ["convert(::Type{T},::T)", "convert(::Type{T},::AbstractString)", "one(::Union{T,Type{T}})"]
    statement := "one(s) and one(T) agree, produce an empty string of zero code units and zero length that is a two-sided identity for *, and convert preserves self-comparison."
    source := "base/strings/basic.jl:227-228,265"
    status := .proven, prop := ``ConvertAllProperty, thm := some ``convertAll_proven },
  { id := "stringscova-basic-getindex-faithful", juliaFile := "base/strings/basic.jl"
    juliaFns := ["first(::AbstractString)", "getindex(::AbstractString,::Integer)",
      "getindex(::AbstractString,::Colon)", "getindex(::AbstractString,::AbstractVector{<:Integer})",
      "getindex(::AbstractString,::AbstractVector{Bool})", "get(::AbstractString,::Integer,default)"]
    statement := "Generic string indexing and get enforce scalar code-unit bounds and character-start validity for arbitrary defaults, first reads index 1, colon preserves indexing, integer vectors collect s[i] in order or fail on out-of-bounds indices, and Bool vectors throw ArgumentError."
    source := "base/strings/basic.jl:183-200"
    status := .proven, prop := ``GetindexProperty, thm := some ``getindex_proven },
  { id := "stringscova-basic-string-faithful", juliaFile := "base/strings/basic.jl"
    juliaFns := ["string()", "string(::AbstractString)"]
    statement := "string() produces an empty string with zero code units, zero length, lastindex 0, and lexicographic order before non-empty strings; string(s) is equal to s under cmp and ==."
    source := "base/strings/basic.jl:217-218"
    status := .proven, prop := ``StringProperty, thm := some ``string_proven },
  { id := "stringscova-basic-isascii-char-faithful", juliaFile := "base/strings/basic.jl"
    juliaFns := ["isascii(::Char)"]
    statement := "Char ASCII classification agrees with AbstractChar < 0x80 on the byte-swapped UInt32 word, accepting 0x00..0x7f in the top byte and rejecting 0x80."
    source := "base/strings/basic.jl:618"
    status := .proven, prop := ``IsasciiCharProperty, thm := some ``isasciiChar_proven },
  { id := "stringscova-basic-eachindex-faithful", juliaFile := "base/strings/basic.jl"
    juliaFns := ["keys(::AbstractString)", "length(::EachStringIndex)", "first(::EachStringIndex)",
      "last(::EachStringIndex)", "iterate(::EachStringIndex)", "eltype(::Type{<:EachStringIndex})"]
    statement := "EachStringIndex has element type Int, starts at 1, terminates immediately on empty strings or indices past ncodeunits, and advances from ncodeunits to ncodeunits+1 before terminating."
    source := "base/strings/basic.jl:580-586"
    status := .proven, prop := ``EachIndexProperty, thm := some ``eachIndex_proven },
  { id := "stringscova-basic-checkbounds-integer-array-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["checkbounds(::Type{Bool},::AbstractString,::AbstractArray{<:Integer})"]
    statement := "The integer-array bounds check succeeds at every BitInteger width iff every iterated index is in 1:ncodeunits(s), short-circuiting on out-of-bounds indices and propagating iterator errors."
    source := "base/strings/basic.jl:210-211"
    status := .proven, prop := ``CheckboundsIntegerArrayProperty, thm := some ``checkboundsIntegerArray_proven },
  { id := "stringscova-basic-cmp-string-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["cmp(::AbstractString,::AbstractString)"]
    statement := "String comparison returns 0 for identical references or equal character sequences, -1 when the left sequence is lexicographically less, 1 when greater, and propagates iterator errors."
    source := "base/strings/basic.jl:308-317"
    status := .proven, prop := ``CmpStringProperty, thm := some ``cmpString_proven },
  { id := "stringscova-basic-isless-string-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["isless(::AbstractString,::AbstractString)"]
    statement := "String ordering is false for identical references and otherwise holds iff the left iterated character sequence is lexicographically less than the right."
    source := "base/strings/basic.jl:355"
    status := .proven, prop := ``IslessStringProperty, thm := some ``islessString_proven },
  { id := "stringscova-basic-checkbounds-real-array-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["checkbounds(::Type{Bool},::AbstractString,::AbstractArray{<:Real})"]
    statement := "The real-array bounds check evaluates scalar bounds across any AbstractArray of Real values, short-circuiting on out-of-bounds integer elements before later non-integer MethodErrors."
    source := "base/strings/basic.jl:208-209"
    status := .proven, prop := ``CheckboundsRealArrayProperty, thm := some ``checkboundsRealArray_proven },
  { id := "stringscova-basic-cmp-symbol-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["cmp(::Symbol,::Symbol)"]
    statement := "Symbol comparison preserves the sign of strcmp and is bounded between -1 and 1."
    source := "base/strings/basic.jl:359-361"
    status := .proven, prop := ``CmpSymbolProperty, thm := some ``cmpSymbol_proven },
  { id := "stringscova-basic-eq-string-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["==(::AbstractString,::AbstractString)"]
    statement := "String equality is true for identical references and otherwise holds iff the iterated character sequences are equal."
    source := "base/strings/basic.jl:335"
    status := .proven, prop := ``EqStringProperty, thm := some ``eqString_proven },
  { id := "stringscova-basic-isascii-string-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["isascii(::AbstractString)"]
    statement := "isascii(::AbstractString) returns true iff every iterated character has codepoint < 0x80, and short-circuits to false on the first non-ASCII character."
    source := "base/strings/basic.jl:619"
    status := .proven, prop := ``IsasciiStringProperty, thm := some ``isasciiString_proven },
  { id := "stringscova-basic-isless-symbol-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["isless(::Symbol,::Symbol)"]
    statement := "Symbol ordering holds iff strcmp is negative, and is false when strcmp is zero."
    source := "base/strings/basic.jl:363"
    status := .proven, prop := ``IslessSymbolProperty, thm := some ``islessSymbol_proven },
  { id := "stringscova-basic-map-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["map(f,::AbstractString)"]
    statement := "String map applies f to arbitrary AbstractChar values, converts each to Char, writes variable-width UTF-8 or custom encodings across buffer resizes, and throws ArgumentError on a non-AbstractChar result."
    source := "base/strings/basic.jl:657-671"
    status := .proven, prop := ``MapProperty, thm := some ``map_proven },
  { id := "stringscova-basic-last-n-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["last(::AbstractString,::Integer)"]
    statement := "last(s, n) throws ArgumentError for negative n and extracts the trailing n characters across arbitrary variable-width AbstractString encodings."
    source := "base/strings/basic.jl:719"
    status := .proven, prop := ``LastNProperty, thm := some ``lastN_proven },
  { id := "stringscova-basic-filter-rebuilt", juliaFile := "base/strings/basic.jl"
    juliaFns := ["filter(f,::AbstractString)"]
    statement := "String filter writes accepted characters in iteration order into any IOBuffer implementation and propagates predicate errors immediately."
    source := "base/strings/basic.jl:673-679"
    status := .proven, prop := ``FilterProperty, thm := some ``filter_proven },
  { id := "strings-basic-index-model", juliaFile := "base/strings/basic.jl"
    juliaFns := ["ncodeunits(::AbstractString)", "codeunit(::AbstractString,::Integer)",
      "isvalid(::AbstractString,::Integer)", "iterate(::AbstractString,::Integer)",
      "eltype(::Type{<:AbstractString})", "sizeof(::AbstractString)",
      "firstindex(::AbstractString)", "isempty(::AbstractString)"]
    statement := "AbstractString interface guarantees codeunit type in UInt8/UInt16/UInt32 and codeunit(s,i) defined iff 1 <= i <= ncodeunits(s); eltype is Char, firstindex is 1, Integer fallbacks throw MethodError on Int64 and convert other widths, and isempty holds iff ncodeunits == 0."
    source := "base/strings/basic.jl:68-181"
    status := .proven, prop := ``StringIndexProperty, thm := some ``stringIndex_proven },
  { id := "strings-basic-bounds-model", juliaFile := "base/strings/basic.jl"
    juliaFns := ["checkbounds(::Type{Bool},::AbstractString,::Integer)",
      "checkbounds(::Type{Bool},::AbstractString,::AbstractRange{<:Integer})",
      "checkbounds(::Type{Bool},::AbstractString,::AbstractArray{<:Real})",
      "checkbounds(::Type{Bool},::AbstractString,::AbstractArray{<:Integer})",
      "checkbounds(::AbstractString,::Union{Integer,AbstractArray})",
      "checkbounds(::Type{Bool},::CodeUnits,::Integer)"]
    statement := "Scalar, range, array, CodeUnits, and throwing bounds checks accept indices in 1:ncodeunits(s) across all BitInteger widths, short-circuit empty or below-1 ranges, and throw BoundsError when out of bounds."
    source := "base/strings/basic.jl:204-213,796"
    status := .proven, prop := ``BoundsModelProperty, thm := some ``boundsModel_proven },
  { id := "strings-basic-presentation", juliaFile := "base/strings/basic.jl"
    juliaFns := ["summary(::IO,::AbstractString)", "*(::Union{AbstractChar,AbstractString},...)",
      "one(::Union{T,Type{T}})", "_isannotated(::Type)", "_isannotated(s)"]
    statement := "summary prints empty when ncodeunits == 0 and the code-unit count otherwise; _isannotated rejects Union{} and accepts only AnnotatedString/AnnotatedChar subtypes; * dispatches to annotatedstring iff any input is annotated."
    source := "base/strings/basic.jl:232-271"
    status := .proven, prop := ``PresentationProperty, thm := some ``presentation_proven },
  { id := "strings-basic-length", juliaFile := "base/strings/basic.jl"
    juliaFns := ["length(::AbstractString)", "length(::AbstractString,::Int,::Int)",
      "length(::AbstractString,::Integer,::Integer)"]
    statement := "length short-circuits lower-bound violations before upper-bound checks, validates endpoint bounds, returns 0 on empty intervals or empty strings, counts validity on single-index intervals, and converts generic BitInteger endpoints."
    source := "base/strings/basic.jl:396-411"
    status := .proven, prop := ``LengthProperty, thm := some ``length_proven },
  { id := "strings-basic-thisind-reverseind", juliaFile := "base/strings/basic.jl"
    juliaFns := ["lastindex(::AbstractString)", "thisind(::AbstractString,::Integer)",
      "thisind(::AbstractString,::Int)", "reverseind(::AbstractString,::Integer)"]
    statement := "thisind fixes 0, 1, ncodeunits+1, and every valid character start while throwing BoundsError outside 0:ncodeunits+1; reverseind(s, 1) equals lastindex(s) and reverseind(s, ncodeunits(s)) equals 1."
    source := "base/strings/basic.jl:180,445-455,742"
    status := .proven, prop := ``ThisindReverseindProperty, thm := some ``thisindReverseind_proven },
  { id := "strings-basic-prevind", juliaFile := "base/strings/basic.jl"
    juliaFns := ["prevind(::AbstractString,::Integer,::Integer)", "prevind(::AbstractString,::Integer)",
      "prevind(::AbstractString,::Int)", "prevind(::AbstractString,::Int,::Int)"]
    statement := "prevind rejects negative counts with ArgumentError, rejects indices outside 1:ncodeunits+1 with BoundsError, fixes ncodeunits+1 at n == 0, and returns 1 - n from index 1."
    source := "base/strings/basic.jl:501-514"
    status := .proven, prop := ``PrevindProperty, thm := some ``prevind_proven },
  { id := "strings-basic-nextind-first", juliaFile := "base/strings/basic.jl"
    juliaFns := ["nextind(::AbstractString,::Integer,::Integer)", "nextind(::AbstractString,::Integer)",
      "nextind(::AbstractString,::Int)", "nextind(::AbstractString,::Int,::Int)",
      "first(::AbstractString,::Integer)"]
    statement := "nextind rejects negative counts with ArgumentError and indices outside 0:ncodeunits with BoundsError, fixes 0 at n == 0, and advances strictly past ncodeunits when ncodeunits + n does not overflow."
    source := "base/strings/basic.jl:560-573,700"
    status := .proven, prop := ``NextindFirstProperty, thm := some ``nextindFirst_proven },
  { id := "strings-basic-isascii-vector", juliaFile := "base/strings/basic.jl"
    juliaFns := ["isascii(::AbstractChar)", "_isascii", "_isascii_chunks",
      "isascii(::AbstractVector{<:Integer})"]
    statement := "isascii(::AbstractChar) checks UInt32(c) < 0x80, and _isascii, _isascii_chunks, and isascii(::AbstractVector) accept UInt8 code-unit vectors whose elements are < 0x80 and reject ranges starting with >= 0x80."
    source := "base/strings/basic.jl:620-653"
    status := .proven, prop := ``IsasciiVectorProperty, thm := some ``isasciiVector_proven },
  { id := "strings-basic-reverse-iterate", juliaFile := "base/strings/basic.jl"
    juliaFns := ["iterate(::Iterators.Reverse{<:AbstractString})",
      "iterate(::Iterators.Reverse{<:EachStringIndex})"]
    statement := "Reverse string and index iterators terminate when the state is below firstindex or the string is empty, and step from index 1 to state 0."
    source := "base/strings/basic.jl:775-776"
    status := .proven, prop := ``ReverseIterateProperty, thm := some ``reverseIterate_proven },
  { id := "strings-basic-codeunits", juliaFile := "base/strings/basic.jl"
    juliaFns := ["codeunit(::AbstractString)", "CodeUnits(::AbstractString)", "sizeof(::CodeUnits)",
      "size(::CodeUnits)", "elsize(::Type{<:CodeUnits})", "getindex(::CodeUnits,::Int)",
      "IndexStyle(::Type{<:CodeUnits})", "checkbounds(::Type{Bool},::CodeUnits,::Integer)",
      "codeunits(::AbstractString)"]
    statement := "codeunits(s) wraps s with element type codeunit(s), linear indexing, byte size equal to sizeof(s) and size(cu,1)*elsize(cu), bounds matching 1:size(cu,1), and indexing consistent with codeunit(s, i)."
    source := "base/strings/basic.jl:82,786-827"
    status := .proven, prop := ``CodeUnitsProperty, thm := some ``codeUnits_proven },
  { id := "strings-basic-split-rest", juliaFile := "base/strings/basic.jl"
    juliaFns := ["_split_rest(::AbstractString,::Int)"]
    statement := "_split_rest splits any variable-width AbstractString into its leading length(s)-n characters and trailing n-character SubString, rethrows non-BoundsError failures, and recovers from BoundsError via _check_length_split_rest(length(s), n)."
    source := "base/strings/basic.jl:829-840"
    status := .proven, prop := ``SplitRestProperty, thm := some ``splitRest_proven }
]

end JuliaLean.Proofs.base.strings.basic
