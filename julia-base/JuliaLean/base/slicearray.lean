import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.abstractarray
import JuliaLean.base.operators
import JuliaLean.base.range
import JuliaLean.base.reshapedarray
import JuliaLean.base.some
import JuliaLean.base.anyall
import JuliaLean.base.show
import JuliaLean.base.strings.io
import JuliaLean.base.tuple
import JuliaLean.base.ntuple

/-!
# Model of `base/slicearray.jl`

Typed source models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform.
Dimension tuples, axis tuples and slice maps are lists, so the model accepts every dimension count
and preserves tuple order.

* A dimension or slice-map value has any `Integer` type: a native `Int`
  (`IntegerValue.native`) or a value of another `Integer` type drawn from an open family
  (`IntegerValue.other code payload`, with `Payload code` the type's own representation:
  fixed-width integers, `Bool`, `BigInt` or a user type). Each tuple element keeps its own type.
* Julia's `Integer` methods on these values dispatch on both argument types. On two native `Int`s
  the model calls the installed `int.jl` methods (`int.le`, `int.eq`, `int.max_BitInteger`);
  every other pair goes to `IntegerMethods`, the methods of the payload types (for built-in
  types the binding supplies the installed `int.jl` models). `max` returns a value of the
  promoted type, so the rank may have a type no dimension has. `convert(Int, x)` returns `Jl`.
* `axes(A, d)` is the installed `abstractarray.axesDim`, reading `axes(A)[d]` with the installed
  `tuple.jl` getters: `getindex(t, ::Int)` for `Int` and the generic `getindex(t, ::Integer)`
  with the payload's `convert(Int, d)` otherwise, so a conversion error propagates.
* `ntuple(f, n)` is the installed `ntuple.jl` method selected by the type of `n`
  (`ntupleInt` or `ntupleInteger`, the checked conversion), its `1:n` range the installed
  `range.unitRangeList`.
* `dim in dims` is `in(x, itr::Tuple) = _in_tuple(x, itr)` (installed `operators.inTuple`) for
  fewer than 32 elements and `in(x, itr::Any32) = invoke(in, Tuple{Any,Any}, x, itr)`
  (installed `operators.inAny32`/`inAny` with the installed `anyall.jl` `any(f, ::Tuple)`) for
  32 or more. `findfirst(isequal(dim), dims)` is the installed `tuple.findFirstTuple`, and
  `something(…, (:))` the installed `some.something`.
* The `DimensionMismatch` messages are `string("Invalid dimension ", dim)` and
  `string("Dimensions ", dims, " are not unique")`, i.e. the installed
  `strings.io.printToString`; a tuple prints with `print(io, x) = show(io, x)` under `lock`
  (installed `show.locked`) and the installed `show.show_Tuple`, an `Int` with the installed
  `show.show_Signed`.
* Methods run in a monad `m` whose exceptions include `ArrayError` (`abstractarray.jl`, carrying
  the shared `JlError` as `ArrayError.julia`), `TupleError` (`tuple.jl`), `NtupleError`
  (`ntuple.jl`) and the `strings/io.jl` printing `Error E`; every exception a callee raises
  propagates unchanged. The one conversion is `tupleToArrayResult`, applied only to
  `getfield` results (see `getfield_error_boundsError`).
-/

namespace JuliaLean.base.slicearray

open JuliaLean

abbrev I64 := JInt .i64
abbrev Result := JuliaLean.base.abstractarray.Result
abbrev ArrayError := JuliaLean.base.abstractarray.ArrayError
abbrev TupleError := JuliaLean.base.tuple.TupleError
abbrev TupleResult := JuliaLean.base.tuple.R
abbrev NtupleError := JuliaLean.base.ntuple.NtupleError

def int (z : Int) : I64 := JInt.lit .i64 z

/-- An `abstractarray.jl` result in the method monad, its exception rethrown unchanged. -/
def liftResult {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {α : Type}
    (r : Result α) : m α :=
  match r with
  | .ok value => pure value
  | .error error => throwThe ArrayError error

/-- A shared `JlError` result in the method monad, as `ArrayError.julia`. -/
def liftJl {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] {α : Type}
    (r : Jl α) : m α :=
  liftResult (JuliaLean.base.abstractarray.liftJulia r)

/-- A `tuple.jl` result in the method monad, its exception rethrown unchanged. -/
def liftTuple {m : Type → Type} [Monad m] [MonadExceptOf TupleError m] {α : Type}
    (r : TupleResult α) : m α :=
  match r with
  | .ok value => pure value
  | .error error => throwThe TupleError error

/-- A `tuple.jl` `getfield` read inside an `abstractarray.jl` method (`axes(A)[d]` in
`axes(A, d)`, whose installed model returns `Result`). `TupleError.julia e` becomes
`ArrayError.julia e` unchanged. `getfield` raises nothing else (`getfield_error_boundsError`), so
the remaining arms are unreachable on every input this lift is applied to; `ArrayError` has no
`TypeError`/`FieldError` constructor to receive them. -/
def tupleToArrayResult {α : Type} (r : TupleResult α) : Result α :=
  r.mapError fun
    | .julia error => .julia error
    | error => .errorException error.kind

theorem getfield_error_boundsError {α : Type} (t : List α) (i : Int) (e : TupleError) :
    JuliaLean.base.tuple.getfield t i = .error e → e = .julia .boundsError := by
  unfold JuliaLean.base.tuple.getfield JuliaLean.base.tuple.bounds
  split
  · split <;> intro h <;> cases h <;> rfl
  · intro h; cases h; rfl

/-- On `getfield` results the lift is `TupleError.julia e ↦ ArrayError.julia e`. -/
theorem tupleToArrayResult_getfield {α : Type} (t : List α) (i : Int) :
    tupleToArrayResult (JuliaLean.base.tuple.getfield t i) =
      match JuliaLean.base.tuple.getfield t i with
      | .ok value => .ok value
      | .error _ => .error (.julia .boundsError) := by
  cases h : JuliaLean.base.tuple.getfield t i with
  | ok value => rfl
  | error e =>
      rw [getfield_error_boundsError t i e h]
      rfl

/-- A value of any `Integer` type: a native `Int`, or a value of the `Integer` type `code`. -/
inductive IntegerValue (Code : Type) (Payload : Code → Type) where
  | native (value : I64)
  | other (code : Code) (value : Payload code)

/-- The methods Julia dispatches to for `Integer` values when an argument is not a native `Int`:
the payload types' own `<=`, `==`, `isequal`, `max` (whose result has the promoted type) and
`convert(Int, x)`. `sameType c c'` is whether two payload codes are the same Julia type (for
`itr isa NTuple`); an `.other` code is never `Int`. -/
structure IntegerMethods (Code : Type) (Payload : Code → Type) where
  le : IntegerValue Code Payload → IntegerValue Code Payload → Bool
  eq : IntegerValue Code Payload → IntegerValue Code Payload → Bool
  isequal : IntegerValue Code Payload → IntegerValue Code Payload → Bool
  max : IntegerValue Code Payload → IntegerValue Code Payload → IntegerValue Code Payload
  convertInt : (code : Code) → Payload code → Jl I64
  sameType : Code → Code → Bool

/-- What `string(x...)` needs to print dimensions. `print(io, x)` and `show(io, x)` of a
non-`Int` payload are the payload type's own methods (`printArg` is its `print_to_string`
argument kind: `StrArg.int32`/`uint64`/… for built-in types, `StrArg.other` otherwise). The
other fields are `show.jl`'s own interface inputs for `show(io, ::Tuple)`: the `Any`-value and
type operations of the `IOContext`, `typeof(dims)`, `printstyled` (util.jl, loaded later),
`===` and `Any`-conversion of the tuple for the `:SHOWN_SET` entry, and the integer-printing
callees and display size `print_to_string` takes. -/
structure IntegerPrinting (E V Ty Code : Type) (Payload : Code → Type) where
  digits : JuliaLean.base.intfuncs.DigitCallees
  displaySize : JInt64 × JInt64
  anyOps : JuliaLean.base.show.AnyOps V Ty
  typeOps : JuliaLean.base.show.TypeOps (JuliaLean.base.strings.io.BufferShowM E) Ty
  tupleType : List (IntegerValue Code Payload) → Ty
  printstyled : JuliaLean.base.show.PrintStyled (JuliaLean.base.strings.io.BufferShowM E) Unit V
  egal : V → List (IntegerValue Code Payload) → Bool
  ofAny : List (IntegerValue Code Payload) → V
  printArg : (code : Code) → Payload code → JuliaLean.base.strings.io.StrArg E V
  showValue : (code : Code) → Payload code → JuliaLean.base.show.JIO Unit V →
    JuliaLean.base.strings.io.BufferShowM E Unit

section Dispatch

variable {Code : Type} {Payload : Code → Type}

/-- `x <= y`: `int.jl`'s `<=` on two `Int`s, otherwise the payload types' method. -/
def integerLe (methods : IntegerMethods Code Payload) :
    IntegerValue Code Payload → IntegerValue Code Payload → Bool
  | .native x, .native y => JuliaLean.base.int.le x y
  | x, y => methods.le x y

/-- `x == y`: `int.jl`'s `==` on two `Int`s, otherwise the payload types' method. -/
def integerEq (methods : IntegerMethods Code Payload) :
    IntegerValue Code Payload → IntegerValue Code Payload → Bool
  | .native x, .native y => JuliaLean.base.int.eq x y
  | x, y => methods.eq x y

/-- `isequal(x, y) = (x == y)::Bool` (operators.jl:196) on two `Int`s, otherwise the payload
types' method. -/
def integerIsequal (methods : IntegerMethods Code Payload) :
    IntegerValue Code Payload → IntegerValue Code Payload → Bool
  | .native x, .native y => JuliaLean.base.int.eq x y
  | x, y => methods.isequal x y

/-- `max(x, y)`: `int.jl`'s `max(x::S, y::T)` for `BitInteger`s on two `Int`s, otherwise the
payload types' method. -/
def integerMax (methods : IntegerMethods Code Payload) :
    IntegerValue Code Payload → IntegerValue Code Payload → IntegerValue Code Payload
  | .native x, .native y => .native (JuliaLean.base.int.max_BitInteger x y)
  | x, y => methods.max x y

/-- A dimension tuple as the heterogeneous tuple of `operators.lean`. -/
def asTuple {V : Type} :
    (values : List V) → JuliaLean.base.operators.HTuple (fun _ : Unit => V) (values.map fun _ => ())
  | [] => .nil
  | value :: values => .cons value (asTuple values)

/-- Whether two `Integer` values have the same Julia type. -/
def sameIntegerType (methods : IntegerMethods Code Payload) :
    IntegerValue Code Payload → IntegerValue Code Payload → Bool
  | .native _, .native _ => true
  | .other c _, .other c' _ => methods.sameType c c'
  | _, _ => false

/-- `itr isa NTuple`: every element has the type of the first. -/
def isNTuple (methods : IntegerMethods Code Payload) : List (IntegerValue Code Payload) → Bool
  | [] => true
  | first :: rest => rest.all (sameIntegerType methods first)

/-- `any(f, itr::Tuple)` (anyall.jl:152-157) with its two installed bodies, `_any(f, itr, :)`
and `_any_tuple`. -/
def anyTuple (methods : IntegerMethods Code Payload) {FT XT : Type} {fTag : FT} {xTag : XT}
    (f : JuliaLean.base.operators.Fix 2
      (IntegerValue Code Payload → IntegerValue Code Payload → Unit → Bool)
      (IntegerValue Code Payload) fTag xTag)
    (itr : List (IntegerValue Code Payload)) :
    Except (JuliaLean.base.anyall.AnyAllError Empty) (Option Bool) :=
  JuliaLean.base.anyall.anyTupleMethod JuliaLean.base.anyall.anyTupleLoop
    JuliaLean.base.anyall.anyTupleStep JuliaLean.base.anyall.anyTupleDone
    (fun y => .ok (.bool (f.f y f.x ()))) (isNTuple methods itr) itr

/-- `x in itr` for a tuple `itr`. Fewer than 32 elements: `in(x, itr::Tuple) = _in_tuple(x, itr)`
(installed `operators.inTuple`, comparing `itr[k] == x`). 32 or more (`Any32`):
`in(x, itr::Any32) = invoke(in, Tuple{Any,Any}, x, itr)`, i.e. `in(x, itr::Any) =
any(==(x), itr)` (installed `operators.inAny32`, `operators.inAny`, `operators.fixEqual`) with
`any(f, ::Tuple)` from `anyall.jl`. `==` on these values never returns `missing` and never
throws, so the `Any32` result is `true` or `false`. -/
def integerIn (methods : IntegerMethods Code Payload) (x : IntegerValue Code Payload)
    (itr : List (IntegerValue Code Payload)) : Bool :=
  if itr.length < 32 then
    match JuliaLean.base.operators.inTuple (Elem := fun _ : Unit => IntegerValue Code Payload)
        (fun {_} value x => if integerEq methods value x then .true else .false) x (asTuple itr) with
    | .true => true
    | _ => false
  else
    match JuliaLean.base.operators.inAny32
        (JuliaLean.base.operators.inAny (fun f itr => anyTuple methods f itr) (integerEq methods))
        x itr with
    | .ok (some true) => true
    | _ => false

/-- The installed `_any(f, itr, :)` loop with a `Bool`-valued, non-throwing `f` returns
`true` or `false`, never `missing` or an exception. -/
theorem anyTupleLoop_bool {α : Type} (p : α → Bool) (itr : List α)
    (colon : JuliaLean.base.anyall.Colon) :
    ∃ b, JuliaLean.base.anyall.anyTupleLoop (ε := Empty) (fun y => .ok (.bool (p y))) itr colon =
      .ok (some b) := by
  unfold JuliaLean.base.anyall.anyTupleLoop
  induction itr with
  | nil => exact ⟨false, by simp [JuliaLean.base.anyall.anyTupleLoop.loop]⟩
  | cons x rest ih =>
      cases h : p x
      · simpa [JuliaLean.base.anyall.anyTupleLoop.loop, h] using ih
      · exact ⟨true, by simp [JuliaLean.base.anyall.anyTupleLoop.loop, h]⟩

/-- The same for the installed `_any_tuple` recursion. -/
theorem anyTupleStep_bool {α : Type} (p : α → Bool) (itr : List α) :
    ∃ b, JuliaLean.base.anyall.anyTupleStep (ε := Empty) JuliaLean.base.anyall.anyTupleDone
      (fun y => .ok (.bool (p y))) false itr = .ok (some b) := by
  induction itr with
  | nil => exact ⟨false, by simp [JuliaLean.base.anyall.anyTupleStep,
      JuliaLean.base.anyall.anyTupleDone]⟩
  | cons x rest ih =>
      cases h : p x
      · simpa [JuliaLean.base.anyall.anyTupleStep, h] using ih
      · exact ⟨true, by simp [JuliaLean.base.anyall.anyTupleStep, h]⟩

/-- `any(f, ::Tuple)` with the `==` callback of `in` returns `.ok (some b)`. -/
theorem anyTuple_bool (methods : IntegerMethods Code Payload) {FT XT : Type} {fTag : FT}
    {xTag : XT}
    (f : JuliaLean.base.operators.Fix 2
      (IntegerValue Code Payload → IntegerValue Code Payload → Unit → Bool)
      (IntegerValue Code Payload) fTag xTag)
    (itr : List (IntegerValue Code Payload)) :
    ∃ b, anyTuple methods f itr = .ok (some b) := by
  unfold anyTuple JuliaLean.base.anyall.anyTupleMethod
  split
  · exact anyTupleLoop_bool (fun y => f.f y f.x ()) itr _
  · exact anyTupleStep_bool (fun y => f.f y f.x ()) itr

/-- On the `Any32` arm the installed `in(x, ::Any32)` returns `.ok (some b)`, and `integerIn` is
that `b`: the `| _ => false` arm only receives `.ok (some false)`. -/
theorem integerIn_any32 (methods : IntegerMethods Code Payload) (x : IntegerValue Code Payload)
    (itr : List (IntegerValue Code Payload)) (hlong : ¬ itr.length < 32) :
    ∃ b, JuliaLean.base.operators.inAny32
        (JuliaLean.base.operators.inAny (fun f itr => anyTuple methods f itr) (integerEq methods))
        x itr = .ok (some b) ∧ integerIn methods x itr = b := by
  obtain ⟨b, hb⟩ := anyTuple_bool methods
    (JuliaLean.base.operators.fixEqual (integerEq methods) x) itr
  refine ⟨b, hb, ?_⟩
  unfold integerIn
  rw [if_neg hlong]
  change (match anyTuple methods (JuliaLean.base.operators.fixEqual (integerEq methods) x) itr with
    | .ok (some true) => true
    | _ => false) = b
  rw [hb]
  cases b <;> rfl

/-- `findfirst(isequal(dim), dims)` as a Julia value: `nothing` or the `Int` position, in the
`some.jl` value type whose payload is a slice-map entry (`none` is `(:)`). -/
def findfirstValue (position : Option Nat) :
    JuliaLean.base.some.Value (Option (IntegerValue Code Payload)) :=
  match position with
  | some i => .scalar (some (.native (int i)))
  | none => .nothing

/-- A slice-map entry from the `some.jl` value `something` returns. -/
def entryOfValue :
    JuliaLean.base.some.Value (Option (IntegerValue Code Payload)) → Option (IntegerValue Code Payload)
  | .scalar entry => entry
  | .some value => entryOfValue value
  | .nothing => none

/-- `something(findfirst(isequal(dim), dims), (:))` with the installed `some.something` returns a
plain value, so `entryOfValue` only ever sees `.scalar`. -/
theorem something_findfirst (position : Option Nat) :
    JuliaLean.base.some.something
        [findfirstValue (Code := Code) (Payload := Payload) position, .scalar none] =
      .ok (.scalar (position.map fun i => .native (int i))) := by
  cases position <;>
    simp [findfirstValue, JuliaLean.base.some.something, JuliaLean.base.some.somethingNothing,
      JuliaLean.base.some.somethingAny]

/-- The elements of `1:n`, the range `ntuple.jl` iterates (`[f(i) for i = 1:n]`). -/
def ntupleRange {m : Type → Type} [Monad m] (n : I64) : m (ULift (List I64)) :=
  pure ⟨JuliaLean.base.range.unitRangeList (int 1) n⟩

/-- `ntuple(f, n)`: `ntuple(f, n::Int)` (ntuple.jl:17) for an `Int`, `ntuple(f, n::Integer)`
(ntuple.jl:33, converting with `convert(Int, n)`) for any other `Integer` type. -/
def ntupleDispatch {m : Type → Type} [Monad m] [MonadExceptOf NtupleError m] {β : Type}
    (methods : IntegerMethods Code Payload) (f : I64 → m β) :
    IntegerValue Code Payload → m (List β)
  | .native n => JuliaLean.base.ntuple.ntupleInt f n ntupleRange
  | .other code n =>
      JuliaLean.base.ntuple.ntupleInteger f (methods.convertInt code) n ntupleRange

/-- `t[d]` for a tuple `t`: `getindex(t, i::Int)` (tuple.jl:33) for an `Int`, the generic
`getindex(t, i::Integer)` (tuple.jl:34) with the payload's `convert(Int, i)` otherwise. -/
def tupleGetindex {α : Type} (methods : IntegerMethods Code Payload) (t : List α) :
    IntegerValue Code Payload → Result α
  | .native i => tupleToArrayResult (JuliaLean.base.tuple.getindexInt t i)
  | .other code i =>
      JuliaLean.base.tuple.getindexInteger
        (convert := ⟨fun i => JuliaLean.base.abstractarray.liftJulia (methods.convertInt code i)⟩)
        t i tupleToArrayResult

end Dispatch

/-! ## Printing dimensions

`show(io, ::Tuple)` is a `partial_fixpoint` loop of `show.jl`, so its monad needs a
`Lean.Order.CCPO` and `MonoBind` structure. `print_to_string` runs its printers in
`strings.io.BufferShowM`, which has none. The order below is the flat order of results with
the divergent run as least element, the construction the installed `iterators.lean` uses for
`Jl`. The instances are `local` to this section, whose only `partial_fixpoint` use is
`show_Tuple` in `tupleArg` on a finite tuple, so the loop ends and the least element is never the
result; no other file sees them. -/

section Messages

open Lean.Order

/-- A buffer state used only inside the divergence marker. -/
def divergenceState : JuliaLean.base.iobuffer.BufferState :=
  { data := [], isMemory := false, reinit := false, readable := false, writable := false,
    seekable := false, append := false, size := int 0, maxsize := int 0, ptr := int 0,
    offset := int 0, mark := int 0 }

/-- The least element: a run that never returns. -/
def divergence {E α : Type} :
    EStateM.Result (JuliaLean.base.strings.io.Error E) JuliaLean.base.iobuffer.BufferState α :=
  .error (.display (.errorException "nontermination")) divergenceState

local instance bufferShowOrder {E α : Type} : PartialOrder (JuliaLean.base.strings.io.BufferShowM E α) :=
  inferInstanceAs (PartialOrder
    (JuliaLean.base.iobuffer.BufferState → FlatOrder (divergence (E := E) (α := α))))

local instance bufferShowCCPO {E α : Type} : CCPO (JuliaLean.base.strings.io.BufferShowM E α) :=
  inferInstanceAs (CCPO
    (JuliaLean.base.iobuffer.BufferState → FlatOrder (divergence (E := E) (α := α))))

local instance bufferShowMonoBind {E : Type} : MonoBind (JuliaLean.base.strings.io.BufferShowM E) where
  bind_mono_left {α β a₁ a₂ f} h := by
    intro s
    have hs : FlatOrder.rel (b := (divergence : EStateM.Result _ _ α)) (a₁ s) (a₂ s) := h s
    show FlatOrder.rel (b := (divergence : EStateM.Result _ _ β))
      (EStateM.bind a₁ f s) (EStateM.bind a₂ f s)
    unfold EStateM.bind
    generalize a₁ s = r at hs ⊢
    cases hs with
    | bot => exact FlatOrder.rel.bot
    | refl => exact FlatOrder.rel.refl
  bind_mono_right {α β a f₁ f₂} h := by
    intro s
    show FlatOrder.rel (b := (divergence : EStateM.Result _ _ β))
      (EStateM.bind a f₁ s) (EStateM.bind a f₂ s)
    unfold EStateM.bind
    cases a s with
    | ok x s' => exact h x s'
    | error e s' => exact FlatOrder.rel.refl

variable {E V Ty Code : Type} {Payload : Code → Type}

/-- `print(io, x)` of one dimension, as a `print_to_string` argument: `Int` is `StrArg.int64`
(the installed `show(io, ::Signed)`), any other type its own `print`. -/
def dimensionArg (printing : IntegerPrinting E V Ty Code Payload) :
    IntegerValue Code Payload → JuliaLean.base.strings.io.StrArg E V
  | .native x => .int64 x
  | .other code x => printing.printArg code x

/-- `show(io, x)` of one element of the tuple. -/
def showDimension (printing : IntegerPrinting E V Ty Code Payload)
    (io : JuliaLean.base.show.JIO Unit V) :
    IntegerValue Code Payload → JuliaLean.base.strings.io.BufferShowM E Unit
  | .native x => JuliaLean.base.show.show_Signed
      (JuliaLean.base.strings.io.bufferPrims printing.displaySize)
      (fun n => JuliaLean.base.show.stringBits printing.digits n
        (JuliaLean.base.show.i64 10) (JuliaLean.base.show.i64 1)) io x
  | .other code x => printing.showValue code x io

/-- `iterate(t::Tuple, i)` (tuple.jl), the installed `tuple.iterateTuple`. -/
def tupleIterOps : JuliaLean.base.show.IterOps (List (IntegerValue Code Payload))
    (IntegerValue Code Payload) Int where
  iterate t := JuliaLean.base.tuple.iterateTuple t 1
  iterateFrom t i := JuliaLean.base.tuple.iterateTuple t i

/-- `print(io, dims)` of a tuple: `print(io, x) = show(io, x)` under `lock` (io.jl), then
`show(io, t::Tuple) = show_delim_array(io, t, '(', ',', ')', true)` (show.jl:1625). -/
def tupleArg (printing : IntegerPrinting E V Ty Code Payload)
    (dims : List (IntegerValue Code Payload)) : JuliaLean.base.strings.io.StrArg E V :=
  .other fun io =>
    let p := JuliaLean.base.strings.io.bufferPrims (E := E) (V := V) printing.displaySize
    JuliaLean.base.show.locked p io
      (JuliaLean.base.show.show_Tuple p printing.anyOps printing.typeOps tupleIterOps
        printing.tupleType printing.printstyled
        (fun n => JuliaLean.base.show.stringBits printing.digits n
          (JuliaLean.base.show.i64 10) (JuliaLean.base.show.i64 1))
        printing.egal printing.ofAny (showDimension printing) io dims)

/-- The `String` literals of the two messages, as their UTF-8 bytes. -/
def invalidDimensionText : JuliaLean.Strings.JStr := ⟨[0x49, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x20, 0x64, 0x69, 0x6d, 0x65, 0x6e, 0x73, 0x69, 0x6f, 0x6e, 0x20], by decide⟩
def dimensionsText : JuliaLean.Strings.JStr := ⟨[0x44, 0x69, 0x6d, 0x65, 0x6e, 0x73, 0x69, 0x6f, 0x6e, 0x73, 0x20], by decide⟩
def notUniqueText : JuliaLean.Strings.JStr := ⟨[0x20, 0x61, 0x72, 0x65, 0x20, 0x6e, 0x6f, 0x74, 0x20, 0x75, 0x6e, 0x69, 0x71, 0x75, 0x65], by decide⟩

/-- A Julia `String` as the `String` an `ArrayError` message holds (UTF-8). -/
def messageText (s : JuliaLean.base.strings.io.JuliaString) : String :=
  String.fromUTF8? ⟨s.bytes.toArray⟩ |>.getD (String.ofList (s.bytes.map fun b => Char.ofNat b.toNat))

/-- `string(xs...) = print_to_string(xs...)` (strings/io.jl), the installed `printToString`; its
exception is rethrown unchanged. -/
def printString {m : Type → Type} [Monad m] [MonadExceptOf (JuliaLean.base.strings.io.Error E) m]
    (printing : IntegerPrinting E V Ty Code Payload)
    (xs : List (JuliaLean.base.strings.io.StrArg E V)) : m String :=
  match JuliaLean.base.strings.io.printToString printing.digits printing.displaySize
      printing.anyOps xs with
  | .ok s => pure (messageText s)
  | .error e => throwThe (JuliaLean.base.strings.io.Error E) e

end Messages

/-- The type of one argument passed to `view`: a colon or an axis element type. -/
inductive SliceViewArgument where
  | colon
  | index (indexType : String)

/-- A `Slices` value. A slice-map entry is `(:)` (`none`) or an `Integer` of any type. -/
structure Slices (Parent Ax Code : Type) (Payload : Code → Type) (N : Nat) where
  parent : Parent
  viewType : String
  slicemap : List (Option (IntegerValue Code Payload))
  axes : List Ax
  axes_length : axes.length = N

def SliceConstruction (Parent Ax Code : Type) (Payload : Code → Type) :=
  Σ N : Nat, Slices Parent Ax Code Payload N

/-- The parent array type's own methods that `Slices` construction calls: every `AbstractArray`
type defines `ndims` (its type parameter `N`), `axes(A)`, and the `Base.OneTo`/`eltype`/`length`
of its axis type. `promoteView` is `Base.promote_op(view, P, argT...)`, a query of the compiler's
type inference, which has no model. -/
structure SliceParentOps (m : Type → Type) (Parent Ax : Type) where
  parentType : String
  ndims : Parent → m I64
  axes : Parent → Result (List Ax)
  oneTo : I64 → Ax
  axisEltype : Ax → String
  axisLength : Ax → m I64
  promoteView : String → List SliceViewArgument → String

/-- The parent's `view(A, I...)` and `setindex!(A, val, I...)` (colon selectors are `none`).
The installed `subarray.viewArray` takes pure normalization and alias functions while the
installed `to_indices` and `unalias` methods are effectful, so these stay inputs until that model
takes an effect monad. -/
structure SliceAccessOps (m : Type → Type) (Parent View Value : Type) where
  view : Parent → List (Option I64) → m View
  setindexParent : Parent → List (Option I64) → Value → m Value

/-- The `dims` argument of `eachslice`: a tuple or a single `Integer`. -/
inductive SliceDims (V : Type) where
  | tuple (dims : List V)
  | integer (dim : V)

/-- An N-index tuple for the fixed-arity `getindex` and `setindex!` methods. -/
structure IntegerIndices (N : Nat) where
  values : List I64
  length_eq : values.length = N

section Methods

variable {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
  [MonadExceptOf TupleError m] [MonadExceptOf NtupleError m]
  {E V Ty : Type} [MonadExceptOf (JuliaLean.base.strings.io.Error E) m]
  {Parent Ax Code : Type} {Payload : Code → Type}

/-- `axes(A, d)`: the installed `abstractarray.axesDim` (abstractarray.jl:79-82). -/
def axesAt (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (a : Parent) (d : IntegerValue Code Payload) : m Ax := do
  let n ← ops.ndims a
  liftResult (JuliaLean.base.abstractarray.axesDim
    (fun d n => integerLe methods d (.native n)) ops.axes (tupleGetindex methods) ops.oneTo n a d)

/--
Julia source: base/slicearray.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unitaxis(::AbstractArray) = Base.OneTo(1)
```
-/
def unitaxis {A Ax' : Type} (oneTo : I64 → Ax') (_array : A) : Ax' := oneTo (int 1)

/--
Julia source: base/slicearray.jl:41-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Slices(A::P, slicemap::SM, ax::AX) where {P,SM,AX}
    length(slicemap) >= ndims(A) ||
        throw(ArgumentError("Slices cannot be constructed with a slicemap of fewer elements than the parent has dimensions"))
    N = length(ax)
    parent_axes = ntuple(d -> axes(A, d), length(slicemap))
    argT = map((a,l) -> l === (:) ? Colon : eltype(a), parent_axes, slicemap)
    S = Base.promote_op(view, P, argT...)
    Slices{P,SM,AX,S,N}(A, slicemap, ax)
end
```
-/
def slicesConstructor (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (a : Parent) (slicemap : List (Option (IntegerValue Code Payload))) (ax : List Ax) :
    m (SliceConstruction Parent Ax Code Payload) := do
  if !(JuliaLean.base.int.le (← ops.ndims a) (int slicemap.length)) then
    throwThe ArrayError (.julia (.argumentError
      "Slices cannot be constructed with a slicemap of fewer elements than the parent has dimensions"))
  let n := ax.length
  let parentAxes ← JuliaLean.base.ntuple.ntupleInt
    (fun d => axesAt ops methods a (.native d)) (int slicemap.length) ntupleRange
  let argT := List.zipWith
    (fun axis entry => match entry with
      | none => .colon
      | some _ => .index (ops.axisEltype axis))
    parentAxes slicemap
  let viewType := ops.promoteView ops.parentType argT
  return ⟨n, { parent := a, viewType, slicemap, axes := ax, axes_length := rfl }⟩

/--
Julia source: base/slicearray.jl:51-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_slice_check_dims() = nothing
```
-/
def sliceCheckDimsEmpty : m Unit := pure ()

/--
Julia source: base/slicearray.jl:52-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _slice_check_dims(dim, dims...)
    1 <= dim || throw(DimensionMismatch("Invalid dimension $dim"))
    dim in dims && throw(DimensionMismatch("Dimensions $dims are not unique"))
    _slice_check_dims(dims...)
end
```
-/
def sliceCheckDims (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload) :
    List (IntegerValue Code Payload) → m Unit
  | [] => sliceCheckDimsEmpty
  | dim :: dims => do
      if !(integerLe methods (.native (int 1)) dim) then
        throwThe ArrayError (.dimensionMismatch (← printString printing
          [.string invalidDimensionText, dimensionArg printing dim]))
      if integerIn methods dim dims then
        throwThe ArrayError (.dimensionMismatch (← printString printing
          [.string dimensionsText, tupleArg printing dims,
            .string notUniqueText]))
      sliceCheckDims methods printing dims

/--
Julia source: base/slicearray.jl:58-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function _eachslice(A::AbstractArray{T,N}, dims::NTuple{M,Integer}, drop::Bool) where {T,N,M}
    _slice_check_dims(dims...)
    N_ = foldl(max, dims; init=N)

    if drop
        # if N = 4, dims = (3,1) then
        # axes = (axes(A,3), axes(A,1))
        # slicemap = (2, :, 1, :)
        ax = map(dim -> axes(A,dim), dims)
        slicemap = ntuple(dim -> something(findfirst(isequal(dim), dims), (:)),  N_)
        return Slices(A, slicemap, ax)
    else
        # if N = 4, dims = (3,1) then
        # axes = (axes(A,1), OneTo(1), axes(A,3), OneTo(1))
        # slicemap = (1, :, 3, :)
        ax = ntuple(dim -> dim in dims ? axes(A,dim) : unitaxis(A), N_)
        slicemap = ntuple(dim -> dim in dims ? dim : (:), N_)
        return Slices(A, slicemap, ax)
    end
end
```
-/
def eachsliceTuple (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload)
    (a : Parent) (dims : List (IntegerValue Code Payload)) (drop : Bool) :
    m (SliceConstruction Parent Ax Code Payload) := do
  sliceCheckDims methods printing dims
  let rank := dims.foldl (integerMax methods) (.native (← ops.ndims a))
  if drop then
    let ax ← dims.mapM (axesAt ops methods a)
    let slicemap ← ntupleDispatch methods (fun dim => do
      let entry ← liftJl (JuliaLean.base.some.something
        [findfirstValue (JuliaLean.base.tuple.findFirstTuple
          (fun d => integerIsequal methods d (.native dim)) dims), .scalar none])
      pure (entryOfValue entry)) rank
    slicesConstructor ops methods a slicemap ax
  else
    let ax ← ntupleDispatch methods (fun dim =>
      if integerIn methods (.native dim) dims then axesAt ops methods a (.native dim)
      else pure (unitaxis ops.oneTo a)) rank
    let slicemap ← ntupleDispatch methods (fun dim => pure
      (if integerIn methods (.native dim) dims then some (IntegerValue.native dim) else none)) rank
    slicesConstructor ops methods a slicemap ax

/--
Julia source: base/slicearray.jl:78-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _eachslice(A::AbstractArray, dim::Integer, drop::Bool)
    _eachslice(A, (dim,), drop)
end
```
-/
def eachsliceDimension (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload)
    (a : Parent) (dim : IntegerValue Code Payload) (drop : Bool) :
    m (SliceConstruction Parent Ax Code Payload) :=
  eachsliceTuple ops methods printing a [dim] drop

/--
Julia source: base/slicearray.jl:132-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function eachslice(A; dims, drop=true)
    _eachslice(A, dims, drop)
end
```
-/
def eachslice (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload)
    (a : Parent) (dims : SliceDims (IntegerValue Code Payload)) (drop : Bool) :
    m (SliceConstruction Parent Ax Code Payload) :=
  match dims with
  | .tuple dims => eachsliceTuple ops methods printing a dims drop
  | .integer dim => eachsliceDimension ops methods printing a dim drop

/--
Julia source: base/slicearray.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrow(A::AbstractMatrix) = _eachslice(A, (1,), true)
```
-/
def eachrowMatrix (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload)
    (a : Parent) : m (SliceConstruction Parent Ax Code Payload) :=
  eachsliceTuple ops methods printing a [.native (int 1)] true

/--
Julia source: base/slicearray.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrow(A::AbstractVector) = eachrow(reshape(A, size(A,1), 1))
```
`size(A, 1)` is the installed `abstractarray.sizeDim` (`Int(1)` by the installed `int.convert`)
over the vector's own `size(A)`; `reshape(A, n, 1)` with two `Int`s is the installed
`reshapedarray.reshapeIntVarargs` (`reshape(parent, dims::Int...)`, reshapedarray.jl:133)
calling the vector type's `reshape(A, dims::Dims)` method (`reshapeDims`): the installed
`reshapeArray` for an `Array`.
-/
def eachrowVector {Vec : Type} (size : Vec → Result (List I64))
    (reshapeDims : Vec → List I64 → m Parent)
    (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload)
    (a : Vec) : m (SliceConstruction Parent Ax Code Payload) := do
  let rows ← liftResult (JuliaLean.base.abstractarray.sizeDim
    (fun d : I64 => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
    size a (int 1))
  let reshaped ← JuliaLean.base.reshapedarray.reshapeIntVarargs reshapeDims a [rows, int 1]
  eachrowMatrix ops methods printing reshaped

/--
Julia source: base/slicearray.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachcol(A::AbstractMatrix) = _eachslice(A, (2,), true)
```
-/
def eachcolMatrix (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload)
    (a : Parent) : m (SliceConstruction Parent Ax Code Payload) :=
  eachsliceTuple ops methods printing a [.native (int 2)] true

/--
Julia source: base/slicearray.jl:210-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachcol(A::AbstractVector) = eachcol(reshape(A, size(A, 1), 1))
```
`size(A, 1)` and `reshape(A, n, 1)` are bound as in `eachrowVector`.
-/
def eachcolVector {Vec : Type} (size : Vec → Result (List I64))
    (reshapeDims : Vec → List I64 → m Parent)
    (ops : SliceParentOps m Parent Ax) (methods : IntegerMethods Code Payload)
    (printing : IntegerPrinting E V Ty Code Payload)
    (a : Vec) : m (SliceConstruction Parent Ax Code Payload) := do
  let rows ← liftResult (JuliaLean.base.abstractarray.sizeDim
    (fun d : I64 => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 d))
    size a (int 1))
  let reshaped ← JuliaLean.base.reshapedarray.reshapeIntVarargs reshapeDims a [rows, int 1]
  eachcolMatrix ops methods printing reshaped

end Methods

/--
Julia source: base/slicearray.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(s::Slices) = s.axes
```
-/
def axes {Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (s : Slices Parent Ax Code Payload N) : List Ax := s.axes

/--
Julia source: base/slicearray.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(s::Slices) = map(length, s.axes)
```
-/
def size {m : Type → Type} [Monad m] {Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (axisLength : Ax → m I64) (s : Slices Parent Ax Code Payload N) : m (List I64) :=
  s.axes.mapM axisLength

/--
Julia source: base/slicearray.jl:236-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _slice_index(s::Slices, c...)
    return map(l -> l === (:) ? (:) : c[l], s.slicemap)
end
```
-/
def sliceIndex {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] [MonadExceptOf TupleError m]
    {Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (methods : IntegerMethods Code Payload) (s : Slices Parent Ax Code Payload N)
    (coordinates : List I64) : m (List (Option I64)) :=
  s.slicemap.mapM fun entry =>
    match entry with
    | none => pure none
    | some (.native l) => do
        let coordinate ← liftTuple (JuliaLean.base.tuple.getindexInt coordinates l)
        pure (some coordinate)
    | some (.other code l) => do
        let coordinate ← JuliaLean.base.tuple.getindexInteger
          (convert := ⟨fun l => liftJl (methods.convertInt code l)⟩) coordinates l liftTuple
        pure (some coordinate)

/--
Julia source: base/slicearray.jl:240-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(s::Slices{P,SM,AX,S,N}, I::Vararg{Int,N}) where {P,SM,AX,S,N}
    @boundscheck checkbounds(s, I...)
    @inbounds view(s.parent, _slice_index(s, I...)...)
end
```
`checkbounds(s, I...)` stays an input: the installed throwing `essentials.checkboundsGeneric`
takes a pure `Bool` check while the installed `abstractarray.checkboundsMany` returns `Result`.
-/
def getindex {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] [MonadExceptOf TupleError m]
    {Parent View Value Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (checkbounds : Slices Parent Ax Code Payload N → IntegerIndices N → m Unit)
    (access : SliceAccessOps m Parent View Value) (methods : IntegerMethods Code Payload)
    (s : Slices Parent Ax Code Payload N) (indices : IntegerIndices N) : m View := do
  checkbounds s indices
  access.view s.parent (← sliceIndex methods s indices.values)

/--
Julia source: base/slicearray.jl:244-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(s::Slices{P,SM,AX,S,N}, val, I::Vararg{Int,N}) where {P,SM,AX,S,N}
    @boundscheck checkbounds(s, I...)
    @inbounds s.parent[_slice_index(s, I...)...] = val
end
```
-/
def setindex! {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m] [MonadExceptOf TupleError m]
    {Parent View Value Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (checkbounds : Slices Parent Ax Code Payload N → IntegerIndices N → m Unit)
    (access : SliceAccessOps m Parent View Value) (methods : IntegerMethods Code Payload)
    (s : Slices Parent Ax Code Payload N) (value : Value) (indices : IntegerIndices N) : m Value := do
  checkbounds s indices
  access.setindexParent s.parent (← sliceIndex methods s indices.values) value

/--
Julia source: base/slicearray.jl:249-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(s::Slices) = s.parent
```
-/
def parent {Parent Ax Code : Type} {Payload : Code → Type} {N : Nat}
    (s : Slices Parent Ax Code Payload N) : Parent := s.parent

end JuliaLean.base.slicearray
