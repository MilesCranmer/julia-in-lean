import JuliaLean.base.iostream
import JuliaLean.Registry.Types


namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (I U Byte M)
open JuliaLean.base.iostream (Handle CInt)
open JuliaLean.base.iostream.Models2Group18

/-- A narrow independent allocation invariant. For every native Int dimension,
all negative lengths and the two excessive positive lengths are rejected before
any runtime primitive is invoked, without changing the world. This quantifies
over every raw runtime implementation with no correctness laws. It covers both
allocation and the zeros composition, so a buggy unchecked allocation or an
ignored allocation error falsifies it. 
Julia source: base/boot.jl:821-824; src/genericmemory.c:55-73
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def ByteInvalidDimensionsRejected : Prop :=
  ∀ (World Vector Memory RootToken : Type)
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (n : I) (world : World),
    (n.val < 0 ∨ (2 : Int) ^ 63 - 2 ≤ n.val) →
      byteVectorUndef runtime n world =
        some (.error (.jl (.argumentError JuliaLean.base.array.genericMemorySizeMessage), world)) ∧
      byteZeros runtime n world =
        some (.error (.jl (.argumentError JuliaLean.base.array.genericMemorySizeMessage), world))

/-- Filling a vector is an in-place operation: whenever it completes, it returns
exactly the original vector identity, under every primitive implementation.
This specifies the alias guarantee independently of the fill algorithm and
assumes no laws for runtime primitives. No proof is supplied.
Julia source: base/array.jl:473-480
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def ByteFillPreservesIdentity : Prop :=
  ∀ (World Vector Memory RootToken : Type)
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (vector : Vector) (value : JuliaLean.base.io.Byte)
    (before after : World) (returned : Vector),
    byteFill runtime vector value before = some (.ok (returned, after)) →
      returned = vector

/-! The following definitions are property instrumentation, not additional Julia
methods. They observe calls made by the actual byteZeros model. Every raw
primitive still runs on the original arbitrary World, with its result, changes,
exception or divergence preserved. No primitive-correctness law is imposed. -/

/-- Observable field results and C-call arguments. A memset event is recorded
before the raw call so that its arguments remain visible even if that call
fails after mutating the world. A successful header event records the actual
returned vector identity, not an assumed relation between heap fields. -/
inductive ByteAllocationAuditEvent (Vector : Type) where
  | header (vector : Vector) (reference : JuliaLean.base.pointer.PointerMemoryRef Byte)
      (dimension : I)
  | reference (vector : Vector) (reference : JuliaLean.base.pointer.PointerMemoryRef Byte)
  | length (vector : Vector) (length : I)
  | memset (pointer : Handle) (value : CInt) (count : U)

abbrev ByteAllocationAuditWorld (World Vector : Type) :=
  World × List (ByteAllocationAuditEvent Vector)

/-- Lift an arbitrary raw IO action, carrying the unchanged audit trace through
both successful and exceptional world updates. Divergence is left as none. -/
def byteAuditLift {World Vector A : Type} (action : M World A) :
    M (ByteAllocationAuditWorld World Vector) A := fun (world, events) =>
  match action world with
  | none => none
  | some (.ok (value, after)) => some (.ok (value, (after, events)))
  | some (.error (error, after)) => some (.error (error, (after, events)))

/-- Append an observation without changing the underlying runtime world. -/
def byteAuditEmit {World Vector : Type} (event : ByteAllocationAuditEvent Vector) :
    M (ByteAllocationAuditWorld World Vector) Unit := fun (world, events) =>
  some (.ok ((), (world, events ++ [event])))

/-- Observe the actual constructed header, ref and length reads and memset
arguments. The remaining primitives are lifted unchanged. No call is replaced
by its hoped-for result, and no raw action can edit the separate audit trace. -/
def byteAuditRuntime {World Vector Memory RootToken : Type}
    (runtime : ByteAllocationRuntime World Vector Memory RootToken) :
    ByteAllocationRuntime (ByteAllocationAuditWorld World Vector) Vector Memory RootToken where
  emptyMemory := byteAuditLift runtime.emptyMemory
  allocateMemoryUnchecked := fun count => byteAuditLift (runtime.allocateMemoryUnchecked count)
  memoryrefNew := fun memory => byteAuditLift (runtime.memoryrefNew memory)
  newVectorHeader := fun reference dimension => do
    let vector ← byteAuditLift (runtime.newVectorHeader reference dimension)
    byteAuditEmit (.header vector reference dimension)
    pure vector
  arrayRef := fun vector => do
    let reference ← byteAuditLift (runtime.arrayRef vector)
    byteAuditEmit (.reference vector reference)
    pure reference
  length := fun vector => do
    let length ← byteAuditLift (runtime.length vector)
    byteAuditEmit (.length vector length)
    pure length
  preserveBegin := fun reference => byteAuditLift (runtime.preserveBegin reference)
  preserveEnd := fun token => byteAuditLift (runtime.preserveEnd token)
  memsetCall := fun pointer value count => do
    byteAuditEmit (.memset pointer value count)
    byteAuditLift (runtime.memsetCall pointer value count)

/-- Last observation of a selected kind. This inspects a trace independently of
byteZeros; it does not execute or duplicate the allocation/fill algorithm. -/
def byteAuditLatest {Vector A : Type}
    (observe : ByteAllocationAuditEvent Vector → Option A)
    (events : List (ByteAllocationAuditEvent Vector)) : Option A :=
  events.foldl (fun latest event =>
    match observe event with
    | none => latest
    | some value => some value) none

def byteAuditLastHeader {Vector : Type} (events : List (ByteAllocationAuditEvent Vector)) :
    Option (Vector × JuliaLean.base.pointer.PointerMemoryRef Byte × I) :=
  byteAuditLatest (fun event => match event with
    | .header vector reference dimension => some (vector, reference, dimension)
    | _ => none) events

def byteAuditLastReference {Vector : Type} (events : List (ByteAllocationAuditEvent Vector)) :
    Option (Vector × JuliaLean.base.pointer.PointerMemoryRef Byte) :=
  byteAuditLatest (fun event => match event with
    | .reference vector reference => some (vector, reference)
    | _ => none) events

def byteAuditLastLength {Vector : Type} (events : List (ByteAllocationAuditEvent Vector)) :
    Option (Vector × I) :=
  byteAuditLatest (fun event => match event with
    | .length vector length => some (vector, length)
    | _ => none) events

def byteAuditMemsets {Vector : Type} (events : List (ByteAllocationAuditEvent Vector)) :
    List (Handle × CInt × U) :=
  events.filterMap (fun event => match event with
    | .memset pointer value count => some (pointer, value, count)
    | _ => none)

/-- Every executed memset requests the zero byte and the complete latest
observed vector length, using UInt ABI reduction on arbitrary primitive
observations. Its destination comes from that same vector's observed reference,
and that vector is the one returned by the header allocator. Pointer equality
uses the installed conversion on the recorded reference, preserving even
nonstandard raw reference metadata rather than assuming a pointer law.

For a genuine UInt8 vector, length is nonnegative and its metadata has the
concrete UInt8 layout, so these conditions mean a zero fill of exactly the
current vector's bytes. No representation or runtime-correctness premise is
needed to state the more general call-argument invariant. -/
def ByteZeroMemsetArguments {Vector : Type}
    (events : List (ByteAllocationAuditEvent Vector)) : Prop :=
  ∀ (before after : List (ByteAllocationAuditEvent Vector))
    (pointer : Handle) (value : CInt) (count : U),
    events = before ++ (.memset pointer value count :: after) →
      value.val = 0 ∧
      ∃ (vector : Vector) (observedLength : I)
        (reference allocatedReference : JuliaLean.base.pointer.PointerMemoryRef Byte)
        (dimension : I),
        byteAuditLastHeader before = some (vector, allocatedReference, dimension) ∧
        byteAuditLastReference before = some (vector, reference) ∧
        byteAuditLastLength before = some (vector, observedLength) ∧
        pointer.address =
          (JuliaLean.base.pointer.unsafeConvertMemoryRefCvoid reference).address ∧
        count.val = observedLength.val % (2 : Int) ^ 64

/-- Independent zero-fill call contract over every native dimension and every
raw runtime, including arbitrary errors and world mutations. Any recorded C
call, including one that raises an exception, must request the zero byte over
the length read from the allocated vector and use its actual reference-derived
pointer. A successful zeros call must issue exactly one such C call, return
the allocated vector identity, and retain the requested constructor dimension.
Thus omitting fill, using a nonzero value, a wrong length, another vector or a
wrong pointer falsifies this contract. No callee-correctness law is assumed.

The outer none case represents divergence in the existing IO semantics, which
provides no completed world or trace to inspect. It does not assert termination
or make claims about opaque C internals. 
Julia source: base/array.jl:473-480,631-653; base/boot.jl:821-824;
base/cmem.jl:40-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def ByteZerosZeroFillArguments : Prop :=
  ∀ (World Vector Memory RootToken : Type)
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (n : I) (world : World),
    match byteZeros (byteAuditRuntime runtime) n (world, []) with
    | none => True
    | some (.error (_, after)) => ByteZeroMemsetArguments after.2
    | some (.ok (vector, after)) =>
        ByteZeroMemsetArguments after.2 ∧
        (byteAuditMemsets after.2).length = 1 ∧
        ∃ reference, byteAuditLastHeader after.2 = some (vector, reference, n)

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.essentials.Models1Group18
open JuliaLean.base.iostream.Models2Group18

/-- An observational syntax-graph path. Indices are mathematical zero-based
positions used only in properties, not Julia arithmetic in an implementation.
The relation observes existing nodes and slots; it neither allocates, copies,
nor interprets syntax. It applies equally to cyclic and shared heaps.
Source representation: base/boot.jl:128-131. -/
def LockMacroAt {Atom : Type} (heap : SyntaxHeap Atom) (start : SyntaxValue Atom) :
    List Nat → SyntaxValue Atom → Prop
  | [], finish => start = finish
  | index :: path, finish =>
    ∃ handle node next,
      start = .exprRef handle ∧
      heap[handle]? = some node ∧
      node.args[index]? = some (some next) ∧
      LockMacroAt heap next path finish

/-- On every valid input graph, @_lock_ios succeeds at the installed logical
allocation boundary and preserves every pre-existing Expr and args slot.
This includes shared/cyclic input, arbitrary syntax heads and literal objects,
and undefined original slots: the macro never reads its input's contents.
All twelve newly allocated Expr objects are fresh, and the result is a valid
reference in a valid heap. The premises are only the installed representation
invariants (valid handles and machine-sized Julia vectors/tuples).
Source: base/iostream.jl:37-47; base/essentials.jl:903; base/boot.jl:128-131.
This states graph preservation, not an expected execution of the model body. -/
def LockIosMacroPreservesInputGraph : Prop :=
  ∀ (Atom : Type) (definitionFile : Option String)
      (stream expression : SyntaxValue (LockMacroAtom Atom))
      (before : SyntaxHeap (LockMacroAtom Atom)),
    syntaxInputValid before [stream, expression] →
    ∃ value after,
      (lockIosMacro definitionFile stream expression).run before = .ok (value, after) ∧
      after.take before.length = before ∧
      after.length = before.length + 12 ∧
      syntaxInputValid after [value, stream, expression] ∧
      ∃ handle, value = .exprRef handle ∧ before.length ≤ handle

/-- The quotation retains one shared stream escape at both property-read
sites, and a distinct escape around the original body syntax. The escaped
payloads are retained by identity, even when stream and body alias or contain
cycles. Neither user expression is captured by the generated local bindings:
both occur inside explicit escape nodes, as specified by esc's documented
hygiene boundary. This statement observes only selected paths and sharing;
it does not reproduce the complete quoted block or its construction order.
Source: base/iostream.jl:38,40-41,43; base/essentials.jl:896-903;
doc/src/devdocs/ast.md (Macros). -/
def LockIosMacroSharesEscapedSyntax : Prop :=
  ∀ (Atom : Type) (definitionFile : Option String)
      (stream expression : SyntaxValue (LockMacroAtom Atom))
      (before : SyntaxHeap (LockMacroAtom Atom)),
    syntaxInputValid before [stream, expression] →
    ∃ value after streamEscape expressionEscape,
      (lockIosMacro definitionFile stream expression).run before = .ok (value, after) ∧
      before.length ≤ streamEscape ∧ before.length ≤ expressionEscape ∧
      streamEscape ≠ expressionEscape ∧
      after[streamEscape]? = some ⟨"escape", [some stream]⟩ ∧
      after[expressionEscape]? = some ⟨"escape", [some expression]⟩ ∧
      LockMacroAt after value [1, 1, 0] (.exprRef streamEscape) ∧
      LockMacroAt after value [3, 1, 0] (.exprRef streamEscape) ∧
      LockMacroAt after value [7, 1] (.exprRef expressionEscape)

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I)
open JuliaLean.base.iostream

/-- A successfully returned RawFD carries the exact descriptor reported by C.
The arbitrary primitive effects include errors and mutations. A successful
wrapped or substituted descriptor would falsify this invariant.
Julia source: `base/iostream.jl:74`, `base/libc.jl:34-35`. -/
def FdReturnedDescriptorExact : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (vectors : JuliaLean.base.iostream.Models2Group18.VectorRefOps World Vector)
    (descriptor : I) (fdEffect : Handle → M World Unit)
    (stream : Stream) (world : World),
    let observedRuntime := { runtime with fd := fun handle => do
      fdEffect handle
      pure descriptor }
    match JuliaLean.base.iostream.Models2Group18.fd access vectors observedRuntime stream world with
    | some (.ok (result, _)) => result.fd.val = descriptor.val
    | _ => True


end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (I M Error)
open JuliaLean.base.iostream (Fields Access Runtime Handle BytePointer Text)
open JuliaLean.base.iostream.Models2Group18

/-- Observe a primitive call without constraining its result, error, mutation,
or termination. The auxiliary event list is specification data, not a Julia
array. It survives every terminating failure. -/
def recordCall {World Event A : Type} (event : Event) (action : M World A) :
    M (List Event × World) A := fun (events, world) =>
  match action world with
  | none => none
  | some (.error (error, after)) => some (.error (error, (events ++ [event], after)))
  | some (.ok (value, after)) => some (.ok (value, (events ++ [event], after)))

/-- The finite observation from any terminating execution. A divergent
execution has no final world, so it cannot make a final-state promise. -/
def hasEvents {World Event A : Type} (expected : List Event)
    (outcome : Option (Except (Error × (List Event × World)) (A × (List Event × World)))) : Prop :=
  match outcome with
  | none => True
  | some (.error (_, (events, _))) => events = expected
  | some (.ok (_, (events, _))) => events = expected

/-- Read the concrete fields of the one stream under observation. All unused
allocation and mutation primitives remain the original supplied operations. -/
def withObservedFields {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (fields : Fields Vector Lock) :
    Access World Stream Vector Lock :=
  { access with get := fun _ => pure fields }

/-- For every possible custom constructor, the default name constructor
requests finalization exactly once, using the original name. Includes errors
and arbitrary result types; no correctness law is imposed on dispatch.
Julia source: `base/iostream.jl:32`. -/
def DefaultConstructorRequestsFinalization : Prop :=
  ∀ (World Name Result : Type) (construct : Name → Bool → M World Result)
    (name : Name) (world : World),
    hasEvents [(name, true)]
      (JuliaLean.base.iostream.newStream
        (fun argument enabled => recordCall (argument, enabled) (construct argument enabled))
        name ([], world))

/-- Turning finalization off makes the entire outcome independent of every
finalizer dispatch choice and operation, including custom methods and the Base
fallback's GC errors and mutations. This applies to every input, custom
constructor and allocation runtime, without assuming any callee law.
Julia source: `base/iostream.jl:24-31`. -/
def FinalizationDisabledIgnoresGC : Prop :=
  ∀ (World Name Vector Memory RootToken Result : Type)
    (bytes : ByteAllocationRuntime World Vector Memory RootToken)
    (ops : ConstructorOps World Name Vector Result)
    (first second : Result → FinalizerSelection World Result)
    (size : I) (name : Name) (world : World),
    newStreamFinalized bytes ops first size name false world =
      newStreamFinalized bytes ops second size name false world

/-- A successful constructor returns the very value produced by selected
construction, even when selected finalization changes the world or returns a
different value. Every constructor and finalizer selection is quantified with
no correctness law. The premises record the actual successful allocation and
construction observations whose identity the whole successful call must retain;
they neither demand successful finalization nor assume the identity conclusion.
Julia source: `base/iostream.jl:24-31`. -/
def FinalizedConstructorPreservesResult : Prop :=
  ∀ (World Name Vector Memory RootToken Result : Type)
    (bytes : ByteAllocationRuntime World Vector Memory RootToken)
    (ops : ConstructorOps World Name Vector Result)
    (finalizerFor : Result → FinalizerSelection World Result)
    (size : I) (name : Name) (finalize : Bool) (chosen returned : Result)
    (buffer : Vector) (before afterAllocation afterConstruction after : World),
    byteZeros bytes size before = some (.ok (buffer, afterAllocation)) →
    ops.withBuffer name buffer afterAllocation = some (.ok (chosen, afterConstruction)) →
    newStreamFinalized bytes ops finalizerFor size name finalize before =
      some (.ok (returned, after)) → returned = chosen

/-- A selected custom finalizer is called exactly once with the fixed close
function and the original object identity. The trace survives custom failures
and arbitrary state changes. The ignored callback result is unrestricted.
This observes the dispatch adapter independently of its code and assumes no
correctness or mutability requirement for a custom method.
Julia source: `base/iostream.jl:28`; Base fallback: `base/gcutils.jl:87-91`. -/
def CustomFinalizerReceivesCloseAndResult : Prop :=
  ∀ (World Result Returned : Type)
    (invoke : CloseFunction → Result → M World Returned)
    (result : Result) (world : World),
    hasEvents [(CloseFunction.close, result)]
      (runSelectedFinalizer
        (.custom (fun function object =>
          recordCall (function, object) (invoke function object)))
        CloseFunction.close result ([], world))

/-- For any constructible UInt8 vector reference, conversion returns its
current address rather than the separately cached IOStream.handle. The only
premises are UInt8 memory-layout invariants. All pointer bits, stream fields,
buffer handles and external states are quantified. Julia source:
`base/iostream.jl:34`; `base/pointer.jl:75-88`. -/
def UnsafeConvertUsesCurrentBackingAddress : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (fields : Fields Vector Lock)
    (references : Vector → JuliaLean.base.pointer.PointerMemoryRef JuliaLean.base.io.Byte)
    (stream : Stream) (world : World),
    (references fields.ios).mem.layoutBytes.val = 1 →
    (references fields.ios).mem.arrayElement ≠ 2 →
    unsafeConvert (withObservedFields access fields) ⟨fun vector => pure (references vector)⟩
      stream world = some (.ok (⟨(references fields.ios).ptr_or_offset⟩, world))

/-- Streams sharing the same byte vector have the same conversion result,
independently of their cached handles, names, marks or locks. This is an
observable alias invariant, not an assumption about pointer conversion.
Julia source: `base/iostream.jl:21,34`. -/
def SharedBufferHasSharedPointer : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (first second : Fields Vector Lock) (stream : Stream) (world : World),
    first.ios = second.ios →
    unsafeConvert (withObservedFields access first) vectors stream world =
      unsafeConvert (withObservedFields access second) vectors stream world

/-- The complete show call passes the original output and name once between
the documented stream delimiters. Every custom print implementation is
allowed, including errors, mutation and non-Unit results. Valid Julia string
size is a representation invariant, not a convenience precondition.
Julia source: `base/iostream.jl:35`. -/
def ShowPreservesNameAndDispatch : Prop :=
  ∀ (World Stream Vector Lock Out Result : Type)
    (access : Access (List (Out × Text × Text × Text) × World) Stream Vector Lock)
    (fields : Fields Vector Lock)
    (print : Out → Text → Text → Text → M World Result)
    (out : Out) (stream : Stream) (world : World),
    fields.name.length < 2 ^ 62 →
    hasEvents [(out, JuliaLean.base.iostream.text "IOStream(", fields.name,
        JuliaLean.base.iostream.text ")")]
      (showStream (withObservedFields access fields)
        ⟨fun output first name last =>
          recordCall (output, first, name, last) (print output first name last)⟩
        out stream ([], world))

/-- Every actual successful custom print result and its complete post-call
world are observable through show. The callback is arbitrary; the premise is
an observed outcome, not a law imposed on all print calls. This rejects a
wrapper that discards the result or resets its state changes.
Julia source: `base/iostream.jl:35`. -/
def ShowForwardsArbitraryResult : Prop :=
  ∀ (World Stream Vector Lock Out Result : Type)
    (access : Access World Stream Vector Lock) (fields : Fields Vector Lock)
    (print : Out → Text → Text → Text → M World Result)
    (out : Out) (stream : Stream) (before after : World) (value : Result),
    print out (JuliaLean.base.iostream.text "IOStream(") fields.name
      (JuliaLean.base.iostream.text ")") before = some (.ok (value, after)) →
    showStream (withObservedFields access fields) ⟨print⟩ out stream before =
      some (.ok (value, after))

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I)
open JuliaLean.base.iostream (Access Runtime CInt Handle)
open JuliaLean.base.iostream.Models2Group18

/-- The generic IO wrapper makes one selected seek request for the original
stream at absolute byte offset zero. No law about the selected seek is used.
Julia source: `base/iostream.jl:185`; seekstart docstring at 165-184. -/
def SeekstartRequestsOrigin : Prop :=
  ∀ (World Stream Result : Type) (ops : SeekOps World Stream Result)
    (stream : Stream) (world : World),
    hasEvents [(stream, JuliaLean.base.io.i 0)]
      (seekstart ⟨fun target offset => recordCall (target, offset) (ops.seek target offset)⟩
        stream ([], world))

/-- A custom seek can return any type and can raise any IO exception after
mutating state. seekstart preserves both outcomes exactly.
Julia source: `base/iostream.jl:185`; doc/src/manual/interfaces.md (I/O). -/
def SeekstartForwardsCustomOutcomes : Prop :=
  ∀ (World Stream Result : Type) (stream : Stream) (before after : World)
    (value : Result) (error : Error),
    seekstart ⟨fun _ _ _ => some (.ok (value, after))⟩ stream before =
      some (.ok (value, after)) ∧
    seekstart (Result := Result) ⟨fun _ _ _ => some (.error (error, after))⟩ stream before =
      some (.error (error, after))


end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I Byte)
open JuliaLean.base.iostream (Fields Access Runtime Handle CInt)
open JuliaLean.base.iostream.Models2Group18

/-- Physical data for the three read-only C query primitives. This is a
specification fixture: the descriptor's invalid sentinel is -1, while the
permission flags are independent of whether the descriptor is closed.
It does not impose a correctness law on a supplied callee. -/
structure QuerySnapshot where
  descriptor : I
  readable : Bool
  writable : Bool

/-- Instantiate the typed foreign query leaves with their concrete snapshot
observations. The source C convention fd != -1 is documented in the installed
Runtime at `src/support/ios.c:723-725`. Other runtime fields stay unrestricted. -/
def querySnapshotRuntime {World Vector : Type}
    (runtime : Runtime World Vector) (snapshot : QuerySnapshot) : Runtime World Vector :=
  { runtime with
    isopen := fun _ => pure (JuliaLean.base.iostream.cint
      (if snapshot.descriptor.val = -1 then 0 else 1))
    readable := fun _ => pure (JuliaLean.base.iostream.cint
      (if snapshot.readable then 1 else 0))
    writable := fun _ => pure (JuliaLean.base.iostream.cint
      (if snapshot.writable then 1 else 0)) }

/-- The stream queries describe the physical descriptor and independent
permission flags, and leave the entire world unchanged. This covers every
descriptor bit pattern, all four flag combinations, every stream field, and
every constructible UInt8 backing reference. The premises are only String
size and UInt8 memory-layout invariants. The expected relation is expressed
in terms of the physical snapshot, not the wrapper's C-status test.
Julia source: `base/iostream.jl:78-88,104-106`; `base/io.jl:163-206`. -/
def StreamQueriesDescribeSnapshot : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (fields : Fields Vector Lock)
    (references : Vector → JuliaLean.base.pointer.PointerMemoryRef Byte)
    (runtime : Runtime World Vector) (snapshot : QuerySnapshot)
    (stream : Stream) (world : World),
    fields.name.length < 2 ^ 62 →
    (references fields.ios).mem.layoutBytes.val = 1 →
    (references fields.ios).mem.arrayElement ≠ 2 →
    let observedFields := { access with get := fun _ => pure fields }
    let observedVectors : VectorRefOps World Vector :=
      ⟨fun vector => pure (references vector)⟩
    let observedRuntime := querySnapshotRuntime runtime snapshot
    ∃ (opened writable readable : Bool),
      isopen observedFields observedVectors observedRuntime stream world =
        some (.ok (opened, world)) ∧
      iswritable observedFields observedVectors observedRuntime stream world =
        some (.ok (writable, world)) ∧
      isreadable observedFields observedVectors observedRuntime stream world =
        some (.ok (readable, world)) ∧
      (opened = true ↔ snapshot.descriptor.val ≠ -1) ∧
      (writable = true ↔ snapshot.descriptor.val ≠ -1 ∧ snapshot.writable = true) ∧
      (readable = true ↔ snapshot.descriptor.val ≠ -1 ∧ snapshot.readable = true)

/-- A closed result prevents both capability queries from consulting either
permission primitive. Changing those primitives cannot change any returned
value, error, mutation, or divergence. Access, vector and open-query effects
are arbitrary, including failures; no callee law is assumed.
Julia source: `base/iostream.jl:104,106`. -/
def ClosedQueriesIgnoreCapabilities : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector)
    (openEffect : Handle → M World Unit)
    (readable1 readable2 writable1 writable2 : Handle → M World CInt)
    (stream : Stream) (world : World),
    let closed := { runtime with isopen := fun handle => do
      openEffect handle
      pure (JuliaLean.base.iostream.cint 0) }
    let first := { closed with readable := readable1, writable := writable1 }
    let second := { closed with readable := readable2, writable := writable2 }
    iswritable access vectors first stream world =
      iswritable access vectors second stream world ∧
    isreadable access vectors first stream world =
      isreadable access vectors second stream world

/-- Error returns from the physical open-query primitive are propagated
unchanged by all three queries, including the primitive's resulting world.
The source's short circuit must not turn an error into a false answer or run
a later capability operation after the failure. Julia source:
`base/iostream.jl:88,104,106`. -/
def StreamQueriesPreservePrimitiveFailure : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (fields : Fields Vector Lock)
    (references : Vector → JuliaLean.base.pointer.PointerMemoryRef Byte)
    (runtime : Runtime World Vector) (failure : Error)
    (stream : Stream) (before after : World),
    fields.name.length < 2 ^ 62 →
    (references fields.ios).mem.layoutBytes.val = 1 →
    (references fields.ios).mem.arrayElement ≠ 2 →
    let observedFields := { access with get := fun _ => pure fields }
    let observedVectors : VectorRefOps World Vector :=
      ⟨fun vector => pure (references vector)⟩
    let observedRuntime := { runtime with
      isopen := fun _ _ => some (.error (failure, after)) }
    isopen observedFields observedVectors observedRuntime stream before =
      some (.error (failure, after)) ∧
    iswritable observedFields observedVectors observedRuntime stream before =
      some (.error (failure, after)) ∧
    isreadable observedFields observedVectors observedRuntime stream before =
      some (.error (failure, after))

/-- IOStream closewrite is a complete no-op, including the entire external
world, for every stream object. Julia source: `base/iostream.jl:95`. -/
def ClosewritePreservesWholeWorld : Prop :=
  ∀ (World Stream : Type) (stream : Stream) (world : World),
    JuliaLean.base.iostream.closewrite (World := World) stream world =
      some (.ok ((), world))


end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M)
open JuliaLean.base.iostream (Access Runtime Handle CInt)
open JuliaLean.base.iostream.Models2Group18

/-- The no-lock EOF result agrees with an independent physical end observation
encoded by the C primitive. Every preceding field/pointer effect, C failure
and divergence remains unrestricted. Julia source: base/iostream.jl:262. -/
def EofReflectsObservedEnd : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector) (effect : Handle → M World Unit) (atEnd : Bool)
    (stream : Stream) (world : World),
    let observed := { runtime with eof := fun pointer => do
      effect pointer
      pure (JuliaLean.base.iostream.cint (if atEnd then 1 else 0)) }
    match eofNolock access vectors observed stream world with
    | some (.ok (result, _)) => result = atEnd
    | _ => True

/-- A closed IOStream may retain buffered input. Its no-lock EOF query is
independent of the open-query primitive, including arbitrary errors, world
changes and divergence. Julia source: base/iostream.jl:78-88,262. -/
def EofIndependentOfOpenQuery : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector) (opened1 opened2 : Handle → M World CInt)
    (stream : Stream) (world : World),
    eofNolock access vectors { runtime with isopen := opened1 } stream world =
      eofNolock access vectors { runtime with isopen := opened2 } stream world

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.iostream (Text text)
open JuliaLean.base.iostream.Models2Group18

/-! These definitions observe calls to the actual model. The separate event
list cannot be mutated by a supplied dispatch operation. Every operation runs
on its original arbitrary World, preserving its result, error and world update.
No selected operation is replaced by a prescribed successful implementation. -/

inductive OpenModeAuditEvent (Name Mode OtherLock NotBool Message Result : Type) where
  | check (mode : Mode) (literal : Text)
  | compared (literal : Text) (answer : Bool ⊕ NotBool)
  | openCall (name : Name) (keywords : OpenModeKeywordList OtherLock)
  | opened (result : Result)
  | interpolate (messagePrefix : Text) (mode : Mode)
  | message (value : Message)
  | makeError (message : Message)
  | madeError (error : Error)

def openModeAuditLift {World Event A : Type} (action : M World A) :
    M (World × List Event) A := fun (world, events) =>
  match action world with
  | none => none
  | some (.ok (value, after)) => some (.ok (value, (after, events)))
  | some (.error (error, after)) => some (.error (error, (after, events)))

def openModeAuditEmit {World Event : Type} (event : Event) :
    M (World × List Event) Unit := fun (world, events) =>
  some (.ok ((), (world, events ++ [event])))

/-- Instrument selected calls without constraining their behavior. Entry
events survive exceptions; returned-value events are recorded only after the
original call succeeds. This is specification instrumentation, not a Julia
implementation or an assumed dispatch-correctness property. -/
def openModeAuditOps {World Name Mode OtherLock NotBool Message Result : Type}
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result) :
    OpenModeOps (World × List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result))
      Name Mode OtherLock NotBool Message Result where
  equals := fun mode literal => do
    openModeAuditEmit (.check mode literal)
    let answer ← openModeAuditLift (ops.equals mode literal)
    openModeAuditEmit (.compared literal answer)
    pure answer
  openFile := fun name keywords => do
    openModeAuditEmit (.openCall name keywords)
    let result ← openModeAuditLift (ops.openFile name keywords)
    openModeAuditEmit (.opened result)
    pure result
  interpolate := fun messagePrefix mode => do
    openModeAuditEmit (.interpolate messagePrefix mode)
    let message ← openModeAuditLift (ops.interpolate messagePrefix mode)
    openModeAuditEmit (.message message)
    pure message
  argumentError := fun message => do
    openModeAuditEmit (.makeError message)
    let error ← openModeAuditLift (ops.argumentError message)
    openModeAuditEmit (.madeError error)
    pure error

def openModeCheckedLiterals {Name Mode OtherLock NotBool Message Result : Type}
    (events : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) : List Text :=
  events.filterMap (fun event => match event with
    | .check _ literal => some literal
    | _ => none)

def openModeAnswers {Name Mode OtherLock NotBool Message Result : Type}
    (events : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) :
    List (Text × (Bool ⊕ NotBool)) :=
  events.filterMap (fun event => match event with
    | .compared literal answer => some (literal, answer)
    | _ => none)

def openModeLastAnswer {Name Mode OtherLock NotBool Message Result : Type}
    (events : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) :
    Option (Text × (Bool ⊕ NotBool)) :=
  events.foldl (fun previous event => match event with
    | .compared literal answer => some (literal, answer)
    | _ => previous) none

def openModeLastMessage {Name Mode OtherLock NotBool Message Result : Type}
    (events : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) : Option Message :=
  events.foldl (fun previous event => match event with
    | .message message => some message
    | _ => previous) none

def openModeReturnedValues {Name Mode OtherLock NotBool Message Result : Type}
    (events : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) : List Result :=
  events.filterMap (fun event => match event with
    | .opened result => some result
    | _ => none)

/-- Interpret a finite trace property on either terminating outcome. Divergence
has no final world in the installed M semantics and makes no trace claim. -/
def OpenModeObserved {World Event A : Type} (property : List Event → Prop)
    (outcome : Option (Except (Error × (World × List Event)) (A × (World × List Event)))) : Prop :=
  match outcome with
  | none => True
  | some (.error (_, (_, events))) => property events
  | some (.ok (_, (_, events))) => property events

/-- Mode tests use the original mode and a prefix of the six source literals,
without reordering, repetition or post-selection tests. This quantifies every
custom equality, opening, interpolation and error constructor, including their
errors, state changes and non-Bool equality results. Source:
base/iostream.jl:399-407. No equality or dispatch-correctness law is assumed. -/
def OpenModeTestsInSourceOrder : Prop :=
  ∀ (World Name Mode OtherLock NotBool Message Result : Type)
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock) (world : World),
    OpenModeObserved (fun events =>
      (∃ remainder, openModeCheckedLiterals events ++ remainder =
        [text "r", text "r+", text "w", text "w+", text "a", text "a+"]) ∧
      ∀ checked literal, OpenModeAuditEvent.check checked literal ∈ events → checked = mode)
      (openMode (openModeAuditOps ops) name mode lock (world, []))

/-- The literal-to-keyword relation of the six source branches. It observes
keyword names, order, presence, fixed true values and the untouched lock value;
it neither calls openMode nor executes its tests. In particular w uses truncate
and w+ keeps truncate before read. Source: base/iostream.jl:400-405. -/
def OpenModeKeywordContract {OtherLock : Type} (lock : Bool ⊕ OtherLock)
    (literal : Text) (actual : OpenModeKeywordList OtherLock) : Prop :=
  ∃ names : List String,
    ((literal = text "r" ∧ names = ["read"]) ∨
     (literal = text "r+" ∧ names = ["read", "write"]) ∨
     (literal = text "w" ∧ names = ["truncate"]) ∨
     (literal = text "w+" ∧ names = ["truncate", "read"]) ∨
     (literal = text "a" ∧ names = ["append"]) ∨
     (literal = text "a+" ∧ names = ["append", "read"])) ∧
    actual = ("lock", lock) :: names.map (fun name => (name, Sum.inl true))

def OpenModeCallObservation {Name Mode OtherLock NotBool Message Result : Type}
    (name : Name) (lock : Bool ⊕ OtherLock)
    (events : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) : Prop :=
  ∀ before after actualName keywords,
    events = before ++ (.openCall actualName keywords :: after) →
    actualName = name ∧
    (∃ literal, openModeLastAnswer before = some (literal, .inl true) ∧
      OpenModeKeywordContract lock literal keywords) ∧
    (after = [] ∨ ∃ result, after = [.opened result])

/-- Every reached selected open receives the original filename, untouched lock
object and the exact source keyword table/order for the observed successful
comparison. The selected call is terminal, even when it fails. Every successful
whole call returns the exact value returned by its single selected open call.
Arbitrary result types and all dispatched callees are quantified; the property
never assumes native string equality or successful custom operations.
Source: base/iostream.jl:399-407. -/
def OpenModeForwardsSelectedKeywordsAndResult : Prop :=
  ∀ (World Name Mode OtherLock NotBool Message Result : Type)
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock) (world : World),
    match openMode (openModeAuditOps ops) name mode lock (world, []) with
    | none => True
    | some (.error (_, (_, events))) => OpenModeCallObservation name lock events
    | some (.ok (result, (_, events))) =>
        OpenModeCallObservation name lock events ∧ openModeReturnedValues events = [result]

/-- A successful non-Bool equality result immediately raises TypeError and
prevents every later selected call. This covers any of the six test positions,
arbitrary non-Bool values, and all preceding custom effects. The class-only
TypeError carrier is the installed boolean-assertion abstraction.
Source: base/iostream.jl:400-405. -/
def OpenModeRejectsNonBooleanEquality : Prop :=
  ∀ (World Name Mode OtherLock NotBool Message Result : Type)
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock) (world : World),
    match openMode (openModeAuditOps ops) name mode lock (world, []) with
    | none => True
    | some (.error (error, (_, events))) =>
        ∀ before after literal bad,
          events = before ++ (.compared literal (.inr bad) :: after) →
          after = [] ∧ error = .foreignError "TypeError" ""
    | some (.ok (_, (_, events))) =>
        ∀ literal bad, OpenModeAuditEvent.compared literal (.inr bad) ∉ events

/-- Invalid-mode reporting begins only after six observed false comparisons,
passes the literal prefix and original mode to the selected interpolation,
and passes its exact result to the selected ArgumentError constructor.
The interpolation result need not be String, and the constructor result need
not itself be an ArgumentError: both are legitimately selected custom calls.
The surrounding method throws the exact constructed value. This observes call
arguments and throw identity rather than recreating the source branch tree.
Source: base/iostream.jl:400-406; base/boot.jl:549-552. -/
def OpenModeInvalidMessageObservation {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode)
    (events : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) : Prop :=
  (∀ before after messagePrefix actualMode,
    events = before ++ (.interpolate messagePrefix actualMode :: after) →
    messagePrefix = text "invalid open mode: " ∧ actualMode = mode ∧
    openModeAnswers before =
      [text "r", text "r+", text "w", text "w+", text "a", text "a+"].map
        (fun literal => (literal, Sum.inl false))) ∧
  (∀ before after message,
    events = before ++ (.makeError message :: after) →
    openModeLastMessage before = some message)

/-- Full-domain invalid-mode reporting and outer throw, including arbitrary
interpolation/constructor exceptions and state changes. A completed custom
exception constructor's returned value is thrown immediately and unchanged.
Source: base/iostream.jl:406. -/
def OpenModePreservesInvalidMessageAndThrow : Prop :=
  ∀ (World Name Mode OtherLock NotBool Message Result : Type)
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock) (world : World),
    match openMode (openModeAuditOps ops) name mode lock (world, []) with
    | none => True
    | some (.error (error, (_, events))) =>
        OpenModeInvalidMessageObservation mode events ∧
        ∀ before after constructed,
          events = before ++ (.madeError constructed :: after) →
          after = [] ∧ error = constructed
    | some (.ok (_, (_, events))) =>
        OpenModeInvalidMessageObservation mode events ∧
        ∀ constructed, OpenModeAuditEvent.madeError constructed ∉ events

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M I Error)
open JuliaLean.base.iostream (Text Handle CInt text)
open JuliaLean.base.iostream.Models2Group18

/-- Successful named fdio returns the exact object produced by the selected
IOStream constructor, even if its Julia type is not IOStream. The first
premise observes that actual call; it assumes no constructor-correctness law.
All property/conversion/GC/C targets, their errors and effects are arbitrary.
Julia source: base/iostream.jl:281-286 (constructor identity invariant). -/
def FdioNamedPreservesConstructedIdentity : Prop :=
  ∀ (World Name Descriptor Result : Type)
    (ops : FdioNamedOps World Name Descriptor Result)
    (iosFd : Handle → I → CInt → CInt → M World Handle)
    (name : Name) (descriptor : Descriptor) (own : Bool)
    (before constructedWorld after : World) (constructed result : Result),
    ops.construct name before = some (.ok (constructed, constructedWorld)) →
    fdioNamed ops iosFd name descriptor own before = some (.ok (result, after)) →
    result = constructed

/-- Constructor failure precedes every property lookup, conversion, GC or C
operation. Its exact exception and post-failure world survive unchanged.
This quantifies over every selected constructor and all remaining operations.
Julia source: base/iostream.jl:281-286 (error precedence). -/
def FdioNamedConstructorFailureFirst : Prop :=
  ∀ (World Name Descriptor Result : Type)
    (ops : FdioNamedOps World Name Descriptor Result)
    (iosFd : Handle → I → CInt → CInt → M World Handle)
    (name : Name) (descriptor : Descriptor) (own : Bool)
    (before after : World) (failure : Error),
    ops.construct name before = some (.error (failure, after)) →
    fdioNamed ops iosFd name descriptor own before = some (.error (failure, after))

/-- A failed Clong cconvert wins over both unsafe conversions, GC preservation
and the C call. The fixture fixes only prior selected calls to successful
values and the single failing conversion; every later operation is arbitrary.
A body that interleaves pointer unsafe_convert before Clong cconvert can
violate this property. Julia source: base/iostream.jl:283-284; manual
calling-c-and-fortran-code.md:248-265. -/
def FdioAllCconvertBeforeUnsafe : Prop :=
  ∀ (World Name Descriptor Result : Type)
    (ops : FdioNamedOps World Name Descriptor Result)
    (iosFd : Handle → I → CInt → CInt → M World Handle)
    (name : Name) (descriptor : Descriptor) (own : Bool)
    (constructed : Result) (ios : ops.IosArgument) (pointerRoot : ops.PointerRoot)
    (before after : World) (failure : Error),
    let failing := { ops with
      construct := fun _ => pure constructed
      getproperty := fun _ _ => pure ios
      cconvertPointer := fun _ => pure pointerRoot
      cconvertLong := fun _ _ => some (.error (failure, after)) }
    fdioNamed failing iosFd name descriptor own before = some (.error (failure, after))

/-- A wrong-type pointer result still permits the later unsafe Clong
conversion to run before foreign-call ABI validation. That later action may
mutate, throw, diverge or return a result of any type: its exception/divergence
wins; on its success the earlier pointer TypeError retains its resulting
world. The scoped fixture executes its actual body, rather than requiring a
law from an arbitrary GC implementation. All selected conversion operations
outside the explicit fixture remain unrestricted.
Julia source: base/iostream.jl:283-284; cached primary compiler source
src/julia-syntax.scm:1069-1106,4861-4897,4973-4982. -/
def FdioAllUnsafeBeforeABI : Prop :=
  ∀ (World Name Descriptor Result : Type)
    (ops : FdioNamedOps World Name Descriptor Result)
    (iosFd : Handle → I → CInt → CInt → M World Handle)
    (name : Name) (descriptor : Descriptor) (own : Bool)
    (constructed : Result) (ios : ops.IosArgument)
    (pointerRoot : ops.PointerRoot) (longRoot : ops.LongRoot)
    (wrongPointer : ops.NotPointer) (pointerEffect : M World Unit)
    (before afterPointer : World),
    pointerEffect before = some (.ok ((), afterPointer)) →
    let observing := { ops with
      construct := fun _ => pure constructed
      getproperty := fun _ _ => pure ios
      cconvertPointer := fun _ => pure pointerRoot
      cconvertLong := fun _ => pure longRoot
      unsafePointer := fun _ => do pointerEffect; pure (.rejected wrongPointer)
      preservation := { ops.preservation with primitive := { ops.preservation.primitive with
        preserveRoots := fun {_} _ body => body } } }
    match ops.unsafeLong longRoot afterPointer with
    | none => fdioNamed observing iosFd name descriptor own before = none
    | some (.error (failure, after)) =>
        fdioNamed observing iosFd name descriptor own before = some (.error (failure, after))
    | some (.ok (_, after)) =>
        fdioNamed observing iosFd name descriptor own before =
          some (.error (.showError .typeError, after))

/-- The common ABI assertion accepts exactly its observed runtime type and
raises the existing TypeError class for every rejected result, preserving the
world. No proposition is supplied by a conversion callback to justify its tag.
Julia source: manual calling-c-and-fortran-code.md:259-265 (foreign-call ABI). -/
def FdioABITypeAssertion : Prop :=
  ∀ (World Expected Other : Type) (value : Expected) (other : Other) (world : World),
    fdioAssertABI (.accepted value :
      JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Expected Other) world =
      some (.ok (value, world)) ∧
    fdioAssertABI (.rejected other :
      JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Expected Other) world =
      some (.error (.showError .typeError, world))

/-- Observations of actual selected calls/results; no model computation is
encoded in the event type. Julia source: base/iostream.jl:287. -/
inductive FdioDefaultEvent (Descriptor Name Result : Type) where
  | string (labelPrefix : Text) (descriptor : Descriptor) (suffix : Text)
  | name (value : Name)
  | fdio (name : Name) (descriptor : Descriptor) (own : Bool)
  | result (value : Result)

/-- Audit a raw selected call, preserving all underlying errors, resulting
worlds and divergence. Entry is recorded even when the call fails; a result
observation is recorded only when that actual call succeeds. -/
def fdioAuditCall {World A Event : Type}
    (entry : Event) (returned : A → Event) (action : M World A) :
    M (List Event × World) A := fun (events, world) =>
  match action world with
  | none => none
  | some (.error (error, after)) => some (.error (error, (events ++ [entry], after)))
  | some (.ok (value, after)) =>
      some (.ok (value, (events ++ [entry, returned value], after)))

/-- Instrument the two permitted dispatch sites without replacing either
selected implementation or losing mutations made before failures. -/
def fdioAuditedOps {World Descriptor Name Result : Type}
    (ops : FdioDefaultOps World Descriptor Name Result) :
    FdioDefaultOps (List (FdioDefaultEvent Descriptor Name Result) × World)
      Descriptor Name Result where
  string := fun labelPrefix descriptor suffix =>
    fdioAuditCall (.string labelPrefix descriptor suffix) .name
      (ops.string labelPrefix descriptor suffix)
  fdio := fun name descriptor own =>
    fdioAuditCall (.fdio name descriptor own) .result (ops.fdio name descriptor own)

/-- The unnamed constructor requests the documented descriptor label, forwards
the actual formatting result and unchanged descriptor/ownership to fdio, and
returns its selected result. Every selected implementation is arbitrary and
may throw, mutate or diverge. The final trace records completed executions;
divergence has no completed trace in the installed IO model.
Julia source: base/iostream.jl:273-279,287. -/
def FdioDefaultArgumentProtocol : Prop :=
  ∀ (World Descriptor Name Result : Type)
    (ops : FdioDefaultOps World Descriptor Name Result)
    (descriptor : Descriptor) (own : Bool) (world : World),
    let request : FdioDefaultEvent Descriptor Name Result :=
      .string (text "<fd ") descriptor (text ">")
    match fdio (fdioAuditedOps ops) descriptor own ([], world) with
    | none => True
    | some (.error (_, (events, _))) =>
        events = [request] ∨
          ∃ name, events = [request, .name name, .fdio name descriptor own]
    | some (.ok (result, (events, _))) =>
        ∃ name, events = [request, .name name, .fdio name descriptor own, .result result]

/-- Formatting failure is propagated with its exact mutated world before any
named-fdio dispatch. This ranges over all arbitrary selected formatters and
subsequent fdio operations, with no formatting correctness hypothesis.
Julia source: base/iostream.jl:287. -/
def FdioDefaultStringFailureFirst : Prop :=
  ∀ (World Descriptor Name Result : Type)
    (ops : FdioDefaultOps World Descriptor Name Result)
    (descriptor : Descriptor) (own : Bool) (before after : World) (failure : Error),
    ops.string (text "<fd ") descriptor (text ">") before = some (.error (failure, after)) →
    fdio ops descriptor own before = some (.error (failure, after))

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (I U Byte M)
open JuliaLean.base.iostream.Models2Group18

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M I U)
open JuliaLean.base.iostream.Models2Group18

/-- Observations of raw allocation, length, header and field primitives, not
assumed storage laws. This trace is disjoint from the arbitrary original world.
Julia source: base/iobuffer.jl:96-107,246-270. -/
structure BufferConstructorAudit (Buffer Memory : Type) where
  allocations : List U := []
  wrapped : List Memory := []
  lengths : List (Memory × I) := []
  headers : List (JuliaLean.base.iobuffer.Fields Memory) := []
  created : List Buffer := []
  observed : List (Buffer × JuliaLean.base.iobuffer.Fields Memory) := []
  writes : List (Buffer × JuliaLean.base.iobuffer.Fields Memory) := []

/-- Record entry and actual successful completion, preserving every underlying
error, result, world change and divergent outcome. -/
def bufferConstructorAuditCall {World Audit A : Type}
    (enter : Audit → Audit) (returned : A → Audit → Audit)
    (action : M World A) : M (Audit × World) A := fun (audit, world) =>
  let audit := enter audit
  match action world with
  | none => none
  | some (.error (error, after)) => some (.error (error, (audit, after)))
  | some (.ok (value, after)) => some (.ok (value, (returned value audit, after)))

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (I U Byte M CancelArg)
open JuliaLean.base.iostream
open JuliaLean.base.iostream.Models2Group18

/-- Instrumentation for a concrete observed IOBuffer header. Reads return its
exact fields and do not modify the arbitrary world; allocations and mutations
remain the supplied primitive operations. This is a concrete field-access
instantiation, not a correctness law for a callee. -/
def withObservedBufferFields {World Buffer Memory : Type}
    (access : JuliaLean.base.iobuffer.Access (M World) Buffer Memory)
    (fields : JuliaLean.base.iobuffer.Fields Memory) :
    JuliaLean.base.iobuffer.Access (M World) Buffer Memory :=
  { access with get := fun _ => pure fields }


end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I U)
open JuliaLean.base.iostream (CInt Handle BytePointer)
open JuliaLean.base.iostream.Models2Group18

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I)
open JuliaLean.base.iostream (Access Runtime CInt)
open JuliaLean.base.iostream.Models2Group18

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I U Byte)
open JuliaLean.base.iostream.Models2Group18

/-- Concrete byte arena for observing only the newly allocated decimal
String. The byte list and store trace are specification data; their size is
created by the native Csize_t allocation request, not an unbounded Julia array
input. The arena does not model or replace any unrelated heap allocation. -/
structure RawFDDecimalArena where
  bytes : List UInt8
  stores : List (I × UInt8)

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.iostream (Access Fields Handle)
open JuliaLean.base.iostream.Models2Group18
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion)

/-- Observe the exact header passed to the raw allocation without replacing
that allocation, its result identity, or any of its effects. The extra header
is specification data. Get and set continue to use the original stream
identity. This is an observation adapter, not a Julia constructor model. -/
def observeInnerAllocation {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) :
    Access World (Stream × Fields Vector Lock) Vector Lock where
  get object := access.get object.1
  set object fields := access.set object.1 fields
  new fields := do
    let object ← access.new fields
    pure (object, fields)

/-- Every successful inner construction requests the original backing vector,
an unset native mark, and enabled locking. It may not substitute a copy of
the vector. The observation retains an arbitrary real allocation and its
state changes. All String and non-String AbstractString inputs, conversion
implementations, lock runtimes, and allocation outcomes are quantified.
Julia source: `base/iostream.jl:21`. -/
def InnerConstructorRetainsBufferAndInitialState : Prop :=
  ∀ (World Name NotString Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector) (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString)
    (name : JuliaLean.Strings.JStr ⊕ Name) (buffer : Vector)
    (before after : World) (object : Stream) (header : Fields Vector Lock),
    newStreamWithBuffer (observeInnerAllocation access) vectors locks names name buffer before =
      some (.ok ((object, header), after)) →
    header.ios = buffer ∧ header.mark.val = -1 ∧ header.dolock = true

/-- A String input is already the declared field type, so replacing the
entire non-String conversion dispatch cannot affect the outcome, including
errors, state changes, or divergence. No conversion law is assumed.
Julia source: `base/iostream.jl:21`; implicit-new lowering in
`src/julia-syntax.scm:3870-3893`. -/
def InnerStringNameBypassesConversion : Prop :=
  ∀ (World Name NotString Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector) (locks : ReentrantRuntime World Lock)
    (first second : InnerNameOps World Name NotString)
    (name : JuliaLean.Strings.JStr) (buffer : Vector) (world : World),
    newStreamWithBuffer access vectors locks first (.inl name) buffer world =
      newStreamWithBuffer access vectors locks second (.inl name) buffer world

/-- A String name's complete byte sequence, including arbitrary malformed
UTF-8, is retained in the new object's allocation request. This is independent
of all supplied operations; the only premise observes actual success.
Julia source: `base/iostream.jl:21`. -/
def InnerStringNamePreservesBytes : Prop :=
  ∀ (World Name NotString Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector) (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString)
    (name : JuliaLean.Strings.JStr) (buffer : Vector)
    (before after : World) (object : Stream) (header : Fields Vector Lock),
    newStreamWithBuffer (observeInnerAllocation access) vectors locks names (.inl name) buffer before =
      some (.ok ((object, header), after)) → header.name = name.bytes

/-- Every String actually produced by selected non-String name conversion is
retained byte for byte when construction succeeds. This quantifies arbitrary
custom return values and mutations rather than assuming conversion preserves
the input's contents. The observations impose no global conversion law.
Julia source: `base/iostream.jl:21`. -/
def InnerConvertedNamePreservesBytes : Prop :=
  ∀ (World Name NotString Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector) (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString) (name : Name) (buffer : Vector)
    (pointer : JuliaLean.base.iostream.BytePointer) (converted : JuliaLean.Strings.JStr)
    (before afterPointer afterConversion after : World)
    (object : Stream) (header : Fields Vector Lock),
    vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) →
    names.convertString name afterPointer = some (.ok (.accepted converted, afterConversion)) →
    newStreamWithBuffer (observeInnerAllocation access) vectors locks names (.inr name) buffer before =
      some (.ok ((object, header), after)) → header.name = converted.bytes

/-- A thrown name-conversion error occurs before lock construction or stream
allocation. The observations are actual individual call outcomes, not laws
requiring the callees to behave correctly. The final world is exactly the
world at conversion failure, even for arbitrary stateful lock runtimes.
Julia source: `base/iostream.jl:21`. -/
def InnerConversionFailurePrecedesLockConstruction : Prop :=
  ∀ (World Name NotString Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector) (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString) (name : Name) (buffer : Vector)
    (pointer : JuliaLean.base.iostream.BytePointer)
    (before afterPointer afterConversion : World) (error : Error),
    vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) →
    names.convertString name afterPointer = some (.error (error, afterConversion)) →
    newStreamWithBuffer access vectors locks names (.inr name) buffer before =
      some (.error (error, afterConversion))

/-- A non-String conversion return is checked by final new, so a subsequent
ReentrantLock-construction error takes precedence over that pending type
error. This distinguishes evaluation from field validation and retains the
actual error's world. All conversion and lock implementations are arbitrary.
Julia source: `base/iostream.jl:21`; `src/datatype.c:1717-1721`. -/
def InnerLockFailurePrecedesReturnedNameTypeError : Prop :=
  ∀ (World Name NotString Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector) (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString) (name : Name) (buffer : Vector)
    (pointer : JuliaLean.base.iostream.BytePointer) (wrong : NotString)
    (before afterPointer afterConversion afterLock : World) (error : Error),
    vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) →
    names.convertString name afterPointer = some (.ok (.rejected wrong, afterConversion)) →
    JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime locks) afterConversion =
      some (.error (error, afterLock)) →
    newStreamWithBuffer access vectors locks names (.inr name) buffer before =
      some (.error (error, afterLock))

/-- A non-String conversion return is rejected after successful concrete
lock construction, retaining its effects and without performing raw stream
allocation. The observable TypeError class and new context are fixed; the
arbitrary wrong value is not silently replaced or converted a second time.
Julia source: `base/iostream.jl:21`; `src/datatype.c:1717-1721`. -/
def InnerReturnedNameTypeErrorKeepsLockEffects : Prop :=
  ∀ (World Name NotString Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector) (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString) (name : Name) (buffer : Vector)
    (pointer : JuliaLean.base.iostream.BytePointer) (wrong : NotString) (mutex : Lock)
    (before afterPointer afterConversion afterLock : World),
    vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) →
    names.convertString name afterPointer = some (.ok (.rejected wrong, afterConversion)) →
    JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime locks) afterConversion =
      some (.ok (mutex, afterLock)) →
    newStreamWithBuffer access vectors locks names (.inr name) buffer before =
      some (.error (.foreignError "TypeError" "new", afterLock))

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.iostream.Models2Group18

/-- The concrete inner lock constructor does not invoke either legacy
whole-constructor slot for the list or SpinLock. Replacing both with arbitrary
throwing, mutating or divergent actions is observationally irrelevant.
Julia source: base/lock.jl:85; base/condition.jl:79; base/locks-mt.jl:46. -/
-- Source: base/lock.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const ThreadSynchronizer = GenericCondition{Threads.SpinLock}
-- /Source
-- Source: base/lock.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ReentrantLock() = new(nothing, 0x0000_0000, 0x00, ThreadSynchronizer())
-- /Source
-- Source: base/condition.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct GenericCondition{L<:AbstractLock}
--     # mutable for identity only
--     const waitq::IntrusiveLinkedList{WaitEntry}
--     const lock::L
-- 
--     GenericCondition{L}() where {L<:AbstractLock} = new{L}(IntrusiveLinkedList{WaitEntry}(), L())
-- /Source
-- Source: base/linked_list.jl:3-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct IntrusiveLinkedList{T}
--     # Invasive list requires that T have a field `.next >: U{T, Nothing}` and `.queue::Any`
--     head::Union{T, Nothing}
--     tail::Union{T, Nothing}
--     IntrusiveLinkedList{T}() where {T} = new{T}(nothing, nothing)
-- /Source
-- Source: base/locks-mt.jl:44-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct SpinLock <: AbstractSpinLock
--     @atomic owned::Int
--     SpinLock() = new(0)
-- /Source
def ReentrantConstructorIgnoresLegacyConstructors : Prop :=
  ∀ (World Lock : Type) (runtime : ReentrantRuntime World Lock)
    (queue : M World runtime.Queue) (spin : M World runtime.SpinLock) (world : World),
    let changed := { runtime with primitive := { runtime.primitive with task := {
      runtime.primitive.task with condition := { runtime.primitive.task.condition with
        newQueue := queue, newLock := spin } } } }
    JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime changed) world =
      JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime runtime) world

/-- Empty wait-queue allocation occurs before SpinLock or ReentrantLock
allocation. Its actual error is propagated with exactly the world reached at
that throw, independently of every later primitive.
Julia source: base/condition.jl:79; base/lock.jl:85. -/
-- Source: base/lock.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const ThreadSynchronizer = GenericCondition{Threads.SpinLock}
-- /Source
-- Source: base/lock.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ReentrantLock() = new(nothing, 0x0000_0000, 0x00, ThreadSynchronizer())
-- /Source
-- Source: base/condition.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct GenericCondition{L<:AbstractLock}
--     # mutable for identity only
--     const waitq::IntrusiveLinkedList{WaitEntry}
--     const lock::L
-- 
--     GenericCondition{L}() where {L<:AbstractLock} = new{L}(IntrusiveLinkedList{WaitEntry}(), L())
-- /Source
-- Source: base/linked_list.jl:3-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct IntrusiveLinkedList{T}
--     # Invasive list requires that T have a field `.next >: U{T, Nothing}` and `.queue::Any`
--     head::Union{T, Nothing}
--     tail::Union{T, Nothing}
--     IntrusiveLinkedList{T}() where {T} = new{T}(nothing, nothing)
-- /Source
-- Source: base/locks-mt.jl:44-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct SpinLock <: AbstractSpinLock
--     @atomic owned::Int
--     SpinLock() = new(0)
-- /Source
def ReentrantQueueFailurePrecedesSpinAllocation : Prop :=
  ∀ (World Lock : Type) (runtime : ReentrantRuntime World Lock)
    (before after : World) (error : Error),
    runtime.allocateQueue none none before = some (.error (error, after)) →
    JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime runtime) before =
      some (.error (error, after))

/-- SpinLock allocation receives the unowned native zero initializer and
precedes the outer ReentrantLock allocation. An observed failure retains
both earlier queue effects and the allocation's own error world.
Julia source: base/locks-mt.jl:46; base/condition.jl:79; base/lock.jl:85. -/
-- Source: base/lock.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const ThreadSynchronizer = GenericCondition{Threads.SpinLock}
-- /Source
-- Source: base/lock.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ReentrantLock() = new(nothing, 0x0000_0000, 0x00, ThreadSynchronizer())
-- /Source
-- Source: base/condition.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct GenericCondition{L<:AbstractLock}
--     # mutable for identity only
--     const waitq::IntrusiveLinkedList{WaitEntry}
--     const lock::L
-- 
--     GenericCondition{L}() where {L<:AbstractLock} = new{L}(IntrusiveLinkedList{WaitEntry}(), L())
-- /Source
-- Source: base/linked_list.jl:3-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct IntrusiveLinkedList{T}
--     # Invasive list requires that T have a field `.next >: U{T, Nothing}` and `.queue::Any`
--     head::Union{T, Nothing}
--     tail::Union{T, Nothing}
--     IntrusiveLinkedList{T}() where {T} = new{T}(nothing, nothing)
-- /Source
-- Source: base/locks-mt.jl:44-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct SpinLock <: AbstractSpinLock
--     @atomic owned::Int
--     SpinLock() = new(0)
-- /Source
def ReentrantSpinFailurePrecedesOuterAllocation : Prop :=
  ∀ (World Lock : Type) (runtime : ReentrantRuntime World Lock)
    (queue : runtime.Queue) (before afterQueue afterSpin : World) (error : Error),
    runtime.allocateQueue none none before = some (.ok (queue, afterQueue)) →
    runtime.spin.newSpinLock (JInt.wrap .i64 0) afterQueue = some (.error (error, afterSpin)) →
    JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime runtime) before =
      some (.error (error, afterSpin))

end JuliaLean.Proofs.base.iostream.Models2Group18


namespace JuliaLean.Proofs.base.iostream.Models2Group18
open JuliaLean
open JuliaLean.base.iostream.Models2Group18

theorem streamBindRun {W A B : Type} (action : JuliaLean.base.io.M W A)
    (next : A → JuliaLean.base.io.M W B) (world : W) :
    (action >>= next) world =
      match action world with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok (value, after)) => next value after := by
  cases ha : action world with
  | none => simp [bind, ha, Option.bind]
  | some outcome =>
    cases outcome with
    | error error => simp [bind, ha, Option.bind]
    | ok pair => cases pair; simp [bind, ha, Option.bind]

theorem streamPureRun {W A : Type} (value : A) (world : W) :
    (pure value : JuliaLean.base.io.M W A) world = some (.ok (value, world)) := rfl

 theorem defaultConstructorRequestsFinalization_proven : DefaultConstructorRequestsFinalization := by
  intro World Name Result construct name world
  simp only [JuliaLean.base.iostream.newStream, recordCall, hasEvents]
  cases construct name true world with
  | none => trivial
  | some result => cases result <;> rfl

 theorem finalizationDisabledIgnoresGC_proven : FinalizationDisabledIgnoresGC := by
  intro World Name Vector Memory RootToken Result bytes ops first second size name world
  rfl

 theorem finalizedConstructorPreservesResult_proven : FinalizedConstructorPreservesResult := by
  intro World Name Vector Memory RootToken Result bytes ops finalizerFor size name finalize chosen returned buffer before afterAllocation afterConstruction after halloc hconstruct h
  simp only [newStreamFinalized, streamBindRun, halloc, hconstruct] at h
  cases finalize with
  | false =>
    simp [streamBindRun, streamPureRun] at h
    exact h.1.symm
  | true =>
    cases hf : runSelectedFinalizer (finalizerFor chosen) CloseFunction.close chosen afterConstruction with
    | none => simp [hf, streamBindRun, streamPureRun] at h
    | some result =>
      cases result with
      | error error => simp [hf, streamBindRun, streamPureRun] at h
      | ok result =>
        simp [hf, streamBindRun, streamPureRun] at h
        exact h.1.symm

 theorem customFinalizerReceivesCloseAndResult_proven : CustomFinalizerReceivesCloseAndResult := by
  intro World Result Returned invoke result world
  simp only [runSelectedFinalizer, streamBindRun, recordCall]
  cases invoke CloseFunction.close result world with
  | none => trivial
  | some outcome => cases outcome <;> rfl

 theorem sharedBufferHasSharedPointer_proven : SharedBufferHasSharedPointer := by
  intro World Stream Vector Lock access vectors first second stream world h
  simp only [unsafeConvert, withObservedFields, streamBindRun, streamPureRun, h]

 theorem showForwardsArbitraryResult_proven : ShowForwardsArbitraryResult := by
  intro World Stream Vector Lock Out Result access fields print out stream before after value h
  simpa only [showStream, withObservedFields, streamBindRun, streamPureRun] using h

 theorem showPreservesNameAndDispatch_proven : ShowPreservesNameAndDispatch := by
  intro World Stream Vector Lock Out Result access fields print out stream world h
  simp only [showStream, withObservedFields, streamBindRun, streamPureRun, recordCall, hasEvents]
  cases print out (JuliaLean.base.iostream.text "IOStream(") fields.name (JuliaLean.base.iostream.text ")") world with
  | none => trivial
  | some result => cases result <;> rfl

 theorem seekstartRequestsOrigin_proven : SeekstartRequestsOrigin := by
  intro World Stream Result ops stream world
  simp only [seekstart, recordCall, hasEvents]
  cases ops.seek stream (JuliaLean.base.io.i 0) world with
  | none => trivial
  | some result => cases result <;> rfl

 theorem seekstartForwardsCustomOutcomes_proven : SeekstartForwardsCustomOutcomes := by
  intro World Stream Result stream before after value error
  exact ⟨rfl, rfl⟩

 theorem closewritePreservesWholeWorld_proven : ClosewritePreservesWholeWorld := by
  intro World Stream stream world
  rfl

 theorem eofIndependentOfOpenQuery_proven : EofIndependentOfOpenQuery := by
  intro World Stream Vector Lock access vectors runtime opened1 opened2 stream world
  rfl

 theorem innerStringNameBypassesConversion_proven : InnerStringNameBypassesConversion := by
  intro World Name NotString Stream Vector Lock access vectors locks first second name buffer world
  rfl

 theorem innerConversionFailurePrecedesLockConstruction_proven :
    InnerConversionFailurePrecedesLockConstruction := by
  intro World Name NotString Stream Vector Lock access vectors locks names name buffer
    pointer before afterPointer afterConversion error hp hc
  simp only [newStreamWithBuffer, sourceNewStreamWithBuffer, streamBindRun, hp, hc]

 theorem innerLockFailurePrecedesReturnedNameTypeError_proven :
    InnerLockFailurePrecedesReturnedNameTypeError := by
  intro World Name NotString Stream Vector Lock access vectors locks names name buffer
    pointer wrong before afterPointer afterConversion afterLock error hp hc hl
  simp only [newStreamWithBuffer, sourceNewStreamWithBuffer, streamBindRun, hp, hc, hl]

 theorem innerReturnedNameTypeErrorKeepsLockEffects_proven :
    InnerReturnedNameTypeErrorKeepsLockEffects := by
  intro World Name NotString Stream Vector Lock access vectors locks names name buffer
    pointer wrong mutex before afterPointer afterConversion afterLock hp hc hl
  simp only [newStreamWithBuffer, sourceNewStreamWithBuffer, streamBindRun, hp, hc, hl]
  rfl

 theorem byteFillPreservesIdentity_proven : ByteFillPreservesIdentity := by
  intro World Vector Memory RootToken runtime vector value before after returned h
  simp only [byteFill, JuliaLean.base.array.fillBytes, streamBindRun, streamPureRun,
    ite_true] at h
  repeat' first | split at h | cases h
  all_goals rfl

 theorem unsafeConvertUsesCurrentBackingAddress_proven :
    UnsafeConvertUsesCurrentBackingAddress := by
  intro World Stream Vector Lock access fields references stream world hs hn
  simp [unsafeConvert, withObservedFields, vectorPointer, bind, pure,
    JuliaLean.base.pointer.cconvertArray, JuliaLean.base.pointer.unsafeConvertMemoryRef,
    JuliaLean.base.pointer.unsafeConvertMemoryRefCvoid, JuliaLean.base.pointer.convertPtrType,
    hs, hn]

 theorem streamQueriesPreservePrimitiveFailure_proven :
    StreamQueriesPreservePrimitiveFailure := by
  intro World Stream Vector Lock access fields references runtime failure stream before after
    hname hs hn
  simp [isopen, iswritable, isreadable, JuliaLean.base.iostream.isopen,
    JuliaLean.base.iostream.iswritable, JuliaLean.base.iostream.isreadable,
    JuliaLean.base.iostream.iosPointer, withVectorPointers, vectorCvoidPointer,
    vectorPointer, bind, pure]

 theorem eofReflectsObservedEnd_proven : EofReflectsObservedEnd := by
  intro World Stream Vector Lock access vectors runtime effect atEnd stream world
  let observed := { runtime with eof := fun pointer => do
    effect pointer
    pure (JuliaLean.base.iostream.cint (if atEnd then 1 else 0)) }
  change (match eofNolock access vectors observed stream world with
    | some (.ok (result, _)) => result = atEnd
    | _ => True)
  simp only [eofNolock, JuliaLean.base.iostream.eofNolock, streamBindRun, streamPureRun]
  cases hp : JuliaLean.base.iostream.iosPointer access
      (withVectorPointers vectors observed) stream world with
  | none => trivial
  | some outcome =>
    cases outcome with
    | error error => trivial
    | ok pair =>
      obtain ⟨pointer, afterPointer⟩ := pair
      simp only [withVectorPointers, observed, streamBindRun, streamPureRun]
      cases he : effect pointer afterPointer with
      | none => trivial
      | some outcome =>
        cases outcome with
        | error error => trivial
        | ok pair => cases pair; cases atEnd <;> rfl

 theorem closedQueriesIgnoreCapabilities_proven : ClosedQueriesIgnoreCapabilities := by
  intro World Stream Vector Lock access vectors runtime openEffect readable1 readable2
    writable1 writable2 stream world
  simp only [iswritable, isreadable, JuliaLean.base.iostream.iswritable,
    JuliaLean.base.iostream.isreadable, JuliaLean.base.iostream.isopen,
    JuliaLean.base.iostream.iosPointer, withVectorPointers, streamBindRun]
  cases hg : access.get stream world with
  | none => exact ⟨rfl, rfl⟩
  | some outcome =>
    cases outcome with
    | error error => exact ⟨rfl, rfl⟩
    | ok pair =>
      obtain ⟨fields, afterFields⟩ := pair
      dsimp only
      cases hp : vectorCvoidPointer vectors fields.ios afterFields with
      | none => exact ⟨rfl, rfl⟩
      | some outcome =>
        cases outcome with
        | error error => exact ⟨rfl, rfl⟩
        | ok pair =>
          obtain ⟨pointer, afterPointer⟩ := pair
          dsimp only
          simp only [streamBindRun, streamPureRun]
          cases he : openEffect pointer afterPointer with
          | none => exact ⟨rfl, rfl⟩
          | some outcome =>
            cases outcome with
            | error error => exact ⟨rfl, rfl⟩
            | ok pair => cases pair; exact ⟨rfl, rfl⟩

 theorem streamQueriesDescribeSnapshot_proven : StreamQueriesDescribeSnapshot := by
  intro World Stream Vector Lock access fields references runtime snapshot stream world
    hname hs hn
  dsimp only
  cases snapshot with
  | mk descriptor readable writable =>
    have hz : (JInt.wrap .i32 0).val = 0 := by rfl
    have ho : (JInt.wrap .i32 1).val = 1 := by rfl
    refine ⟨decide (descriptor.val ≠ -1), decide (descriptor.val ≠ -1) && writable,
      decide (descriptor.val ≠ -1) && readable, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      cases readable <;> cases writable <;>
        by_cases hd : descriptor.val = -1 <;>
        simp [isopen, iswritable, isreadable, JuliaLean.base.iostream.isopen,
          JuliaLean.base.iostream.iswritable, JuliaLean.base.iostream.isreadable,
          querySnapshotRuntime, JuliaLean.base.iostream.iosPointer, withVectorPointers,
          vectorCvoidPointer, vectorPointer, bind, pure, JuliaLean.base.iostream.cint,
          hz, ho, hd]

open JuliaLean
open JuliaLean.base.io (I U Byte M Error)
open JuliaLean.base.iostream (Handle BytePointer CInt Text Access Fields Runtime text)
open JuliaLean.base.iostream.Models2Group18
open JuliaLean.base.essentials.Models1Group18
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion)

/-! ## Monadic stepping helpers for `JuliaLean.base.io.M` -/

theorem streamBindOfOk {W A B : Type} {action : JuliaLean.base.io.M W A}
    {next : A → JuliaLean.base.io.M W B} {before mid : W} {value : A}
    (h : action before = some (.ok (value, mid))) :
    (action >>= next) before = next value mid := by
  rw [streamBindRun, h]

theorem streamBindOfError {W A B : Type} {action : JuliaLean.base.io.M W A}
    {next : A → JuliaLean.base.io.M W B} {before after : W} {error : JuliaLean.base.io.Error}
    (h : action before = some (.error (error, after))) :
    (action >>= next) before = some (.error (error, after)) := by
  rw [streamBindRun, h]

theorem streamBindOfNone {W A B : Type} {action : JuliaLean.base.io.M W A}
    {next : A → JuliaLean.base.io.M W B} {before : W}
    (h : action before = none) :
    (action >>= next) before = none := by
  rw [streamBindRun, h]

theorem streamBindEqOk {W A B : Type} {action : JuliaLean.base.io.M W A}
    {next : A → JuliaLean.base.io.M W B} {before after : W} {result : B}
    (h : (action >>= next) before = some (.ok (result, after))) :
    ∃ value mid, action before = some (.ok (value, mid)) ∧
      next value mid = some (.ok (result, after)) := by
  rw [streamBindRun] at h
  cases ha : action before with
  | none => rw [ha] at h; cases h
  | some outcome =>
    cases outcome with
    | error error => rw [ha] at h; cases h
    | ok pair =>
      obtain ⟨value, mid⟩ := pair
      rw [ha] at h
      exact ⟨value, mid, rfl, h⟩

def zeroCInt : CInt :=
  ⟨0, by change -(2 ^ 31 : Int) ≤ 0 ∧ (0 : Int) ≤ 2 ^ 31 - 1; omega⟩

def zeroByte : Byte :=
  ⟨0, by change (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 2 ^ 8 - 1; omega⟩

theorem liftJlConvertI32Zero {W : Type} :
    (JuliaLean.base.io.liftJl (JInt.convert (IntTy.i32.name) .i32 0) :
      JuliaLean.base.io.M W CInt) =
      pure zeroCInt := rfl

theorem liftJlConvertI32ZeroRun {W : Type} (world : W) :
    JuliaLean.base.io.liftJl (JInt.convert (IntTy.i32.name) .i32 0) world =
      some (.ok (zeroCInt, world)) := rfl

theorem liftJlZeroU8 {W : Type} :
    (JuliaLean.base.io.liftJl
      (JuliaLean.base.number.zeroType
        (fun (_ : Unit) n => JInt.convert (IntTy.u8.name) .u8 n) ()) :
      JuliaLean.base.io.M W Byte) =
      pure zeroByte := rfl

theorem liftJlConvertI32ZeroByte {W : Type} :
    (JuliaLean.base.io.liftJl (JInt.convert (IntTy.i32.name) .i32 zeroByte.val) :
      JuliaLean.base.io.M W CInt) =
      pure zeroCInt := rfl
/-! ## `fdio` properties -/

theorem fdioNamedPreservesConstructedIdentity_proven : FdioNamedPreservesConstructedIdentity := by
  intro World Name Descriptor Result ops iosFd name descriptor own
    before constructedWorld after constructed result hconstruct h
  unfold fdioNamed at h
  rw [streamBindOfOk hconstruct] at h
  rcases streamBindEqOk h with ⟨ios, w1, _, h⟩
  rcases streamBindEqOk h with ⟨pointerRoot, w2, _, h⟩
  rcases streamBindEqOk h with ⟨longRoot, w3, _, h⟩
  rcases streamBindEqOk h with ⟨zero, w4, _, h⟩
  dsimp only at h
  rcases streamBindEqOk h with ⟨_, w5, _, h⟩
  rw [streamPureRun] at h
  cases h
  rfl

theorem fdioNamedConstructorFailureFirst_proven : FdioNamedConstructorFailureFirst := by
  intro World Name Descriptor Result ops iosFd name descriptor own before after failure h
  unfold fdioNamed
  exact streamBindOfError h

theorem fdioAllCconvertBeforeUnsafe_proven : FdioAllCconvertBeforeUnsafe := by
  intro World Name Descriptor Result ops iosFd name descriptor own
    constructed ios pointerRoot before after failure failing
  simp only [fdioNamed, failing, streamBindRun, streamPureRun]

theorem fdioABITypeAssertion_proven : FdioABITypeAssertion := by
  intro World Expected Other value other world
  exact ⟨rfl, rfl⟩

theorem fdioAllUnsafeBeforeABI_proven : FdioAllUnsafeBeforeABI := by
  intro World Name Descriptor Result ops iosFd name descriptor own
    constructed ios pointerRoot longRoot wrongPointer pointerEffect
    before afterPointer hpe observing
  have hpe2 : observing.unsafePointer pointerRoot before =
      some (.ok (.rejected wrongPointer, afterPointer)) := by
    dsimp only [observing]
    rw [streamBindOfOk hpe, streamPureRun]
  unfold fdioNamed
  dsimp only [observing, JuliaLean.base.gcutils.withPreservedRoots]
  rw [streamBindOfOk rfl, streamBindOfOk rfl, streamBindOfOk rfl, streamBindOfOk rfl,
    streamBindOfOk (liftJlConvertI32ZeroRun before)]
  rw [streamBindRun, streamBindOfOk hpe2]
  cases hl : ops.unsafeLong longRoot afterPointer with
  | none =>
    rw [streamBindOfNone hl]
  | some outcome =>
    cases outcome with
    | error pair =>
      obtain ⟨failure, after⟩ := pair
      rw [streamBindOfError hl]
    | ok pair =>
      obtain ⟨_, after⟩ := pair
      rw [streamBindOfOk hl]
      rfl

theorem fdioDefaultArgumentProtocol_proven : FdioDefaultArgumentProtocol := by
  intro World Descriptor Name Result ops descriptor own world request
  simp only [fdio, fdioAuditedOps, fdioAuditCall, streamBindRun]
  cases hs : ops.string (text "<fd ") descriptor (text ">") world with
  | none => trivial
  | some outcome =>
    cases outcome with
    | error pair =>
      cases pair
      exact Or.inl rfl
    | ok pair =>
      obtain ⟨name, afterString⟩ := pair
      dsimp only
      cases hf : ops.fdio name descriptor own afterString with
      | none => trivial
      | some outcome =>
        cases outcome with
        | error pair =>
          cases pair
          exact Or.inr ⟨name, rfl⟩
        | ok pair =>
          obtain ⟨result, _⟩ := pair
          exact ⟨name, rfl⟩

theorem fdioDefaultStringFailureFirst_proven : FdioDefaultStringFailureFirst := by
  intro World Descriptor Name Result ops descriptor own before after failure h
  unfold fdio
  exact streamBindOfError h

/-! ## Inner `IOStream(name, buf)` buffer and byte invariants -/

theorem newStreamWithBuffer_observeInnerAllocation_eq_ok
    {World Name NotString Stream Vector Lock : Type}
    {access : Access World Stream Vector Lock}
    {vectors : VectorRefOps World Vector}
    {locks : ReentrantRuntime World Lock}
    {names : InnerNameOps World Name NotString}
    {name : JuliaLean.Strings.JStr ⊕ Name} {buffer : Vector}
    {before after : World} {object : Stream}
    {header : Fields Vector Lock}
    (h : newStreamWithBuffer (observeInnerAllocation access) vectors locks names name buffer before =
      some (.ok ((object, header), after))) :
    ∃ (pointer : BytePointer) (afterPointer afterConversion : World)
      (value : JuliaLean.Strings.JStr) (mutex : Lock),
      vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) ∧
      (match name with
        | .inl v =>
            (pure (TypeAssertion.accepted v) :
              M World (TypeAssertion JuliaLean.Strings.JStr NotString))
        | .inr v => names.convertString v) afterPointer =
        some (.ok (.accepted value, afterConversion)) ∧
      header = {
        handle := JuliaLean.base.pointer.convertPtrType pointer
        ios := buffer
        name := value.bytes
        mark := JuliaLean.base.io.i (-1)
        mutex := mutex
        dolock := true } := by
  unfold newStreamWithBuffer sourceNewStreamWithBuffer at h
  rcases streamBindEqOk h with ⟨pointer, afterPointer, hp, h⟩
  dsimp only at h
  have hstep :
      ∃ (converted : TypeAssertion JuliaLean.Strings.JStr NotString) (afterConversion : World),
        (match name with
          | .inl v =>
              (pure (TypeAssertion.accepted v) :
                M World (TypeAssertion JuliaLean.Strings.JStr NotString))
          | .inr v => names.convertString v) afterPointer =
          some (.ok (converted, afterConversion)) ∧
        (do
          let mutex ← JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime locks)
          match converted with
          | .accepted value =>
              (observeInnerAllocation access).new {
                handle := JuliaLean.base.pointer.convertPtrType pointer
                ios := buffer
                name := value.bytes
                mark := JuliaLean.base.io.i (-1)
                mutex := mutex
                dolock := true }
          | .rejected _ => throw (Error.foreignError "TypeError" "new")) afterConversion =
          some (.ok ((object, header), after)) := by
    cases name with
    | inl v =>
      rcases streamBindEqOk h with ⟨converted, afterConversion, hc, h⟩
      exact ⟨converted, afterConversion, hc, h⟩
    | inr v =>
      rcases streamBindEqOk h with ⟨converted, afterConversion, hc, h⟩
      exact ⟨converted, afterConversion, hc, h⟩
  rcases hstep with ⟨converted, afterConversion, hc, h⟩
  rcases streamBindEqOk h with ⟨mutex, afterLock, _, h⟩
  cases converted with
  | rejected _ =>
    cases h
  | accepted value =>
    unfold observeInnerAllocation at h
    dsimp only at h
    rcases streamBindEqOk h with ⟨_, _, _, h⟩
    rw [streamPureRun] at h
    cases h
    exact ⟨pointer, afterPointer, afterConversion, value, mutex, hp, hc, rfl⟩
theorem innerConstructorRetainsBufferAndInitialState_proven :
    InnerConstructorRetainsBufferAndInitialState := by
  intro World Name NotString Stream Vector Lock access vectors locks names
    name buffer before after object header h
  rcases newStreamWithBuffer_observeInnerAllocation_eq_ok h with ⟨_, _, _, _, _, _, _, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

theorem innerStringNamePreservesBytes_proven : InnerStringNamePreservesBytes := by
  intro World Name NotString Stream Vector Lock access vectors locks names
    name buffer before after object header h
  rcases newStreamWithBuffer_observeInnerAllocation_eq_ok h with
    ⟨_, _, _, value, _, _, hc, rfl⟩
  dsimp only [streamPureRun] at hc
  cases hc
  rfl

theorem innerConvertedNamePreservesBytes_proven : InnerConvertedNamePreservesBytes := by
  intro World Name NotString Stream Vector Lock access vectors locks names
    name buffer pointer converted before afterPointer afterConversion after
    object header hp hc h
  rcases newStreamWithBuffer_observeInnerAllocation_eq_ok h with
    ⟨pointer', afterPointer', afterConversion', value, _, hp', hc', rfl⟩
  rw [hp] at hp'
  cases hp'
  dsimp only at hc'
  rw [hc] at hc'
  cases hc'
  rfl

/-! ## `fd` exact RawFD descriptor property -/

theorem rawFDOfInteger_exact {W : Type} (value : Int) (world : W) :
    match JuliaLean.base.libc.rawFDOfInteger value world with
    | some (.ok (result, _)) => result.fd.val = value
    | _ => True := by
  unfold JuliaLean.base.libc.rawFDOfInteger JuliaLean.base.libc.convertTo
    JuliaLean.base.io.liftJl JInt.convert
  rw [streamBindRun]
  by_cases hc : IntTy.i32.min ≤ value ∧ value ≤ IntTy.i32.max
  · rw [dif_pos hc]
    rfl
  · rw [dif_neg hc]
    trivial
theorem fdReturnedDescriptorExact_proven : FdReturnedDescriptorExact := by
  intro World Stream Vector Lock access runtime vectors descriptor fdEffect stream world observedRuntime
  unfold JuliaLean.base.iostream.Models2Group18.fd JuliaLean.base.iostream.fd
  rw [streamBindRun]
  cases JuliaLean.base.iostream.iosPointer access
      (withVectorPointers vectors observedRuntime) stream world with
  | none => trivial
  | some outcome =>
    cases outcome with
    | error _ => trivial
    | ok pair =>
      rcases pair with ⟨pointer, afterPointer⟩
      dsimp only [withVectorPointers, observedRuntime]
      rw [streamBindRun, streamBindRun]
      cases fdEffect pointer afterPointer with
      | none => trivial
      | some outcome =>
        cases outcome with
        | error _ => trivial
        | ok pair =>
          rcases pair with ⟨_, afterEffect⟩
          dsimp only [streamPureRun]
          exact rawFDOfInteger_exact descriptor.val afterEffect

/-! ## Byte allocation and zero-fill properties -/

theorem byteInvalidDimensionsBounds (n : I)
    (h : n.val < 0 ∨ (2 : Int) ^ 63 - 2 ≤ n.val) :
    (n.val % 2 ^ 64).toNat ≠ 0 ∧
      JuliaLean.base.array.maxIntVal - 1 ≤ (n.val % 2 ^ 64).toNat := by
  have hn := n.2
  change -(2 ^ 63 : Int) ≤ n.val ∧ n.val ≤ (2 ^ 63 : Int) - 1 at hn
  change (n.val % 2 ^ 64).toNat ≠ 0 ∧ (2 ^ 63 - 1) - 1 ≤ (n.val % 2 ^ 64).toNat
  omega

theorem memoryUndef_of_invalid {World Mem : Type}
    (empty : ByteAllocationM World Mem) (allocate : Nat → ByteAllocationM World Mem) (n : I)
    (h : n.val < 0 ∨ (2 : Int) ^ 63 - 2 ≤ n.val) :
    JuliaLean.base.array.memoryUndef (some byteAllocationLayout) empty allocate n =
      throw (JuliaLean.base.array.Error.argument JuliaLean.base.array.genericMemorySizeMessage) := by
  obtain ⟨hnel0, hnelBig⟩ := byteInvalidDimensionsBounds n h
  unfold JuliaLean.base.array.memoryUndef JuliaLean.base.array.memorynew
    JuliaLean.base.array.allocGenericMemory byteAllocationLayout
    JuliaLean.base.array.newGenericMemory
  simp only [hnel0, ↓reduceIte, ge_iff_le, hnelBig, decide_true, Bool.true_or]
  rfl
theorem byteInvalidDimensionsRejected_proven : ByteInvalidDimensionsRejected := by
  intro World Vector Memory RootToken runtime n world h
  have hUndef :
      byteVectorUndef runtime n world =
        some (.error (.jl (.argumentError JuliaLean.base.array.genericMemorySizeMessage), world)) := by
    unfold byteVectorUndef JuliaLean.base.array.arrayUndef1
    rw [memoryUndef_of_invalid _ _ n h]
    rfl
  refine ⟨hUndef, ?_⟩
  unfold byteZeros JuliaLean.base.array.constant637
  exact streamBindOfError hUndef

theorem byteZeroMemsetArguments_nil {Vector : Type} :
    ByteZeroMemsetArguments ([] : List (ByteAllocationAuditEvent Vector)) := by
  intro before after pointer value count h
  cases before <;> simp at h

theorem byteZeroMemsetArguments_one {Vector : Type}
    (v : Vector) (ar : JuliaLean.base.pointer.PointerMemoryRef Byte) (d : I) :
    ByteZeroMemsetArguments [.header v ar d] := by
  intro before after pointer value count h
  rcases before with _ | ⟨b1, before⟩ <;> simp at h

theorem byteZeroMemsetArguments_two {Vector : Type}
    (v : Vector) (ar r : JuliaLean.base.pointer.PointerMemoryRef Byte) (d : I) :
    ByteZeroMemsetArguments [.header v ar d, .reference v r] := by
  intro before after pointer value count h
  rcases before with _ | ⟨b1, _ | ⟨b2, before⟩⟩ <;> simp at h

theorem byteZeroMemsetArguments_four {Vector : Type}
    (v : Vector) (ar r : JuliaLean.base.pointer.PointerMemoryRef Byte) (d l : I) :
    let p := JuliaLean.base.pointer.unsafeConvertMemoryRefCvoid r
    let cnt := JInt.rem .u64 l
    let events : List (ByteAllocationAuditEvent Vector) :=
      [.header v ar d, .reference v r, .length v l, .memset p zeroCInt cnt]
    ByteZeroMemsetArguments events ∧
      (byteAuditMemsets events).length = 1 ∧
      byteAuditLastHeader events = some (v, ar, d) := by
  intro p cnt events
  refine ⟨?_, rfl, rfl⟩
  intro before after pointer value count h
  rcases before with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before⟩⟩⟩⟩ <;>
    simp [events] at h
  rcases h with ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩
  refine ⟨rfl, v, l, r, ar, d, rfl, rfl, rfl, rfl, rfl⟩

theorem byteAllocationLift_audit_run {World Vector A : Type}
    (action : M World A) (w : World)
    (ev : List (ByteAllocationAuditEvent Vector)) :
    (byteAllocationLift (byteAuditLift action)).run (w, ev) =
      match action w with
      | none => none
      | some (.error (err, w')) => some (.error (err, (w', ev)))
      | some (.ok (val, w')) => some (.ok (.ok val, (w', ev))) := by
  simp only [byteAllocationLift, ExceptT.lift, ExceptT.mk, ExceptT.run,
    Functor.map, byteAuditLift]
  cases action w with
  | none => rfl
  | some outcome =>
    cases outcome with
    | error pair => cases pair; rfl
    | ok pair => cases pair; rfl


theorem byteAllocationLiftRun {W A : Type} (action : M W A) (w : W) :
    (byteAllocationLift action).run w =
      match action w with
      | none => none
      | some (.error err) => some (.error err)
      | some (.ok (val, w')) => some (.ok (.ok val, w')) := by
  simp only [byteAllocationLift, ExceptT.lift, ExceptT.mk, ExceptT.run, Functor.map]
  cases action w with
  | none => rfl
  | some outcome =>
    cases outcome with
    | error _ => rfl
    | ok pair => cases pair; rfl
theorem byteAllocationBindRun {W A B : Type}
    (m : ByteAllocationM W A) (f : A → ByteAllocationM W B) (w : W) :
    (m >>= f).run w =
      match m.run w with
      | none => none
      | some (.error err) => some (.error err)
      | some (.ok (.error err, w')) => some (.ok (.error err, w'))
      | some (.ok (.ok val, w')) => (f val).run w' := by
  dsimp only [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, ExceptT.bindCont]
  cases m w with
  | none => rfl
  | some outcome =>
    cases outcome with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨res, w'⟩
      cases res <;> rfl

theorem memoryUndef_byteAudit_events {World Vector Memory RootToken : Type}
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (n : I) (world : World) :
    match (JuliaLean.base.array.memoryUndef (some byteAllocationLayout)
      (byteAllocationLift (byteAuditRuntime runtime).emptyMemory)
      (fun count => byteAllocationLift ((byteAuditRuntime runtime).allocateMemoryUnchecked count))
      n).run (world, []) with
    | none => True
    | some (.error (_, after)) => after.2 = []
    | some (.ok (.error _, after)) => after.2 = []
    | some (.ok (.ok _, after)) => after.2 = [] := by
  unfold JuliaLean.base.array.memoryUndef JuliaLean.base.array.memorynew
    JuliaLean.base.array.allocGenericMemory byteAllocationLayout
    JuliaLean.base.array.newGenericMemory
  dsimp only [byteAuditRuntime]
  by_cases h0 : (n.val % 2 ^ 64).toNat = 0
  · rw [if_pos h0, byteAllocationLift_audit_run]
    cases runtime.emptyMemory world with
    | none => trivial
    | some outcome =>
      cases outcome with
      | error pair => cases pair; rfl
      | ok pair => cases pair; rfl
  · rw [if_neg h0, if_neg h0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hcond :
        (decide ((n.val % 2 ^ 64).toNat ≥ JuliaLean.base.array.maxIntVal - 1) ||
          decide ((JuliaLean.base.array.sizeMulOverflow (n.val % 2 ^ 64).toNat 1).1 ≥
            JuliaLean.base.array.maxIntVal - 1) ||
          (JuliaLean.base.array.sizeMulOverflow (n.val % 2 ^ 64).toNat 1).2) = true
    · rw [if_pos hcond]
      rfl
    · rw [if_neg hcond, byteAllocationLift_audit_run]
      cases runtime.allocateMemoryUnchecked (n.val % 2 ^ 64).toNat world with
      | none => trivial
      | some outcome =>
        cases outcome with
        | error pair => cases pair; rfl
        | ok pair => cases pair; rfl

theorem byteVectorUndef_byteAudit {World Vector Memory RootToken : Type}
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (n : I) (world : World) :
    match byteVectorUndef (byteAuditRuntime runtime) n (world, []) with
    | none => True
    | some (.error (_, after)) => after.2 = []
    | some (.ok (vector, after)) =>
        ∃ allocatedRef, after.2 = [.header vector allocatedRef n] := by
  have hm := memoryUndef_byteAudit_events runtime n world
  unfold byteVectorUndef runByteAllocation JuliaLean.base.array.arrayUndef1
  rw [streamBindRun, byteAllocationBindRun]
  cases hmem : (JuliaLean.base.array.memoryUndef (some byteAllocationLayout)
      (byteAllocationLift (byteAuditRuntime runtime).emptyMemory)
      (fun count => byteAllocationLift ((byteAuditRuntime runtime).allocateMemoryUnchecked count))
      n).run (world, []) with
  | none => trivial
  | some outcome =>
    rw [hmem] at hm
    cases outcome with
    | error pair =>
      rcases pair with ⟨err, w1, ev1⟩
      exact hm
    | ok pair =>
      rcases pair with ⟨res, w1, ev1⟩
      cases res with
      | error err =>
        exact hm
      | ok memory =>
        dsimp only at hm ⊢
        subst ev1
        rw [byteAllocationBindRun]
        dsimp only [byteAuditRuntime]
        rw [byteAllocationLift_audit_run]
        cases href : runtime.memoryrefNew memory w1 with
        | none => trivial
        | some outcome =>
          cases outcome with
          | error pair =>
            cases pair
            rfl
          | ok pair =>
            rcases pair with ⟨allocatedRef, w2⟩
            dsimp only
            rw [byteAllocationLiftRun, streamBindRun]
            dsimp only [byteAuditLift, byteAuditEmit, streamBindRun, streamPureRun]
            cases hhdr : runtime.newVectorHeader allocatedRef n w2 with
            | none => trivial
            | some outcome =>
              cases outcome with
              | error pair =>
                cases pair
                rfl
              | ok pair =>
                rcases pair with ⟨vector, w3⟩
                exact ⟨allocatedRef, rfl⟩

theorem byteZerosZeroFillArguments_proven : ByteZerosZeroFillArguments := by
  intro World Vector Memory RootToken runtime n world
  have hUndef := byteVectorUndef_byteAudit runtime n world
  unfold byteZeros JuliaLean.base.array.constant637
  rw [streamBindRun]
  dsimp only
  cases hu : byteVectorUndef (byteAuditRuntime runtime) n (world, []) with
  | none => trivial
  | some outcome =>
    rw [hu] at hUndef
    cases outcome with
    | error pair =>
      rcases pair with ⟨err, w1, ev1⟩
      dsimp only at hUndef ⊢
      subst ev1
      exact byteZeroMemsetArguments_nil
    | ok pair =>
      rcases pair with ⟨vector, w1, ev1⟩
      rcases hUndef with ⟨allocatedRef, hEv1⟩
      dsimp only at hEv1
      subst ev1
      dsimp only
      rw [liftJlZeroU8, streamBindRun, streamPureRun]
      unfold byteFill JuliaLean.base.array.fillBytes byteMemset
      simp only [byteAuditRuntime, byteAuditLift, byteAuditEmit,
        liftJlConvertI32ZeroByte, id, ↓reduceIte, streamBindRun, streamPureRun]
      cases hr : runtime.arrayRef vector w1 with
      | none => trivial
      | some outcome =>
        cases outcome with
        | error pair =>
          cases pair
          exact byteZeroMemsetArguments_one vector allocatedRef n
        | ok pair =>
          rcases pair with ⟨ref, w2⟩
          dsimp only [List.cons_append, List.nil_append]
          cases hp : runtime.preserveBegin ref w2 with
          | none => trivial
          | some outcome =>
            cases outcome with
            | error pair =>
              cases pair
              exact byteZeroMemsetArguments_two vector allocatedRef ref n
            | ok pair =>
              rcases pair with ⟨token, w3⟩
              dsimp only
              cases hl : runtime.length vector w3 with
              | none => trivial
              | some outcome =>
                cases outcome with
                | error pair =>
                  cases pair
                  exact byteZeroMemsetArguments_two vector allocatedRef ref n
                | ok pair =>
                  rcases pair with ⟨len, w4⟩
                  dsimp only [List.cons_append, List.nil_append]
                  have h4 := byteZeroMemsetArguments_four vector allocatedRef ref n len
                  cases hm : runtime.memsetCall
                      (JuliaLean.base.pointer.unsafeConvertMemoryRefCvoid ref)
                      zeroCInt (JInt.rem .u64 len) w4 with
                  | none => trivial
                  | some outcome =>
                    cases outcome with
                    | error pair =>
                      cases pair
                      exact h4.1
                    | ok pair =>
                      rcases pair with ⟨_, w5⟩
                      dsimp only
                      cases he : runtime.preserveEnd token w5 with
                      | none => trivial
                      | some outcome =>
                        cases outcome with
                        | error pair =>
                          cases pair
                          exact h4.1
                        | ok pair =>
                          rcases pair with ⟨_, w6⟩
                          exact ⟨h4.1, h4.2.1, allocatedRef, h4.2.2⟩

/-! ## `@_lock_ios` syntax-graph properties -/

theorem lockMacroSyntaxBindRun {Atom A B : Type} (m : SyntaxM Atom A)
    (f : A → SyntaxM Atom B) (heap : SyntaxHeap Atom) :
    ((m >>= f).run heap) =
      match m.run heap with
      | .error e => .error e
      | .ok (a, heap') => (f a).run heap' := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  cases m heap with
  | error e => rfl
  | ok pair => cases pair; rfl

theorem lockMacroSyntaxExprRun {Atom : Type} (head : String)
    (args : List (SyntaxValue Atom)) (heap : SyntaxHeap Atom) :
    (syntaxExpr head args).run heap =
      .ok (.exprRef heap.length, heap ++ [⟨head, args.map some⟩]) := rfl

theorem syntaxExprAppendBind {Atom A : Type} (head : String)
    (args : List (SyntaxValue Atom))
    (next : SyntaxValue Atom → SyntaxM Atom A)
    (before extra : SyntaxHeap Atom) :
    ((syntaxExpr head args >>= next).run (before ++ extra)) =
      (next (.exprRef (before.length + extra.length))).run
        (before ++ (extra ++ [⟨head, args.map some⟩])) := by
  rw [lockMacroSyntaxBindRun, lockMacroSyntaxExprRun, List.length_append, List.append_assoc]

theorem syntaxExprAppendLast {Atom : Type} (head : String)
    (args : List (SyntaxValue Atom))
    (before extra : SyntaxHeap Atom) :
    (syntaxExpr head args).run (before ++ extra) =
      .ok (.exprRef (before.length + extra.length),
        before ++ (extra ++ [⟨head, args.map some⟩])) := by
  rw [lockMacroSyntaxExprRun, List.length_append, List.append_assoc]

def lockIosExtra {Atom : Type} (definitionFile : Option String)
    (stream expression : SyntaxValue (LockMacroAtom Atom)) (n : Nat) :
    SyntaxHeap (LockMacroAtom Atom) :=
  [ ⟨"escape", [some stream]⟩,
    ⟨".", [some (.exprRef n), some (.atom (.quotedSymbol "_dolock"))]⟩,
    ⟨"=", [some (.symbol "l"), some (.exprRef (n + 1))]⟩,
    ⟨".", [some (.exprRef n), some (.atom (.quotedSymbol "lock"))]⟩,
    ⟨"=", [some (.symbol "temp"), some (.exprRef (n + 3))]⟩,
    ⟨"call", [some (.symbol "lock"), some (.symbol "temp")]⟩,
    ⟨"&&", [some (.symbol "l"), some (.exprRef (n + 5))]⟩,
    ⟨"escape", [some expression]⟩,
    ⟨"=", [some (.symbol "val"), some (.exprRef (n + 7))]⟩,
    ⟨"call", [some (.symbol "unlock"), some (.symbol "temp")]⟩,
    ⟨"&&", [some (.symbol "l"), some (.exprRef (n + 9))]⟩,
    ⟨"block", [
      some (.atom (.lineNumber (JInt.wrap .i64 40) definitionFile)), some (.exprRef (n + 2)),
      some (.atom (.lineNumber (JInt.wrap .i64 41) definitionFile)), some (.exprRef (n + 4)),
      some (.atom (.lineNumber (JInt.wrap .i64 42) definitionFile)), some (.exprRef (n + 6)),
      some (.atom (.lineNumber (JInt.wrap .i64 43) definitionFile)), some (.exprRef (n + 8)),
      some (.atom (.lineNumber (JInt.wrap .i64 44) definitionFile)), some (.exprRef (n + 10)),
      some (.atom (.lineNumber (JInt.wrap .i64 45) definitionFile)), some (.symbol "val")]⟩ ]

theorem lockIosMacroRun {Atom : Type} (definitionFile : Option String)
    (stream expression : SyntaxValue (LockMacroAtom Atom))
    (before : SyntaxHeap (LockMacroAtom Atom)) :
    (lockIosMacro definitionFile stream expression).run before =
      .ok (.exprRef (before.length + 11),
        before ++ lockIosExtra definitionFile stream expression before.length) := by
  conv => lhs; rw [← List.append_nil before]
  unfold lockIosMacro
  rw [syntaxExprAppendBind, syntaxExprAppendBind, syntaxExprAppendBind,
    syntaxExprAppendBind, syntaxExprAppendBind, syntaxExprAppendBind,
    syntaxExprAppendBind, syntaxExprAppendBind, syntaxExprAppendBind,
    syntaxExprAppendBind, syntaxExprAppendBind, syntaxExprAppendLast]
  rfl

theorem lockMacroValueValidLength {Atom : Type} {before after : SyntaxHeap Atom}
    (h : before.length ≤ after.length) (value : SyntaxValue Atom)
    (hv : syntaxValueValid before value) : syntaxValueValid after value := by
  cases value with
  | atom _ => trivial
  | symbol _ => trivial
  | exprRef n => exact Nat.lt_of_lt_of_le hv h

def lockMacroNodeValid {Atom : Type} (heap : SyntaxHeap Atom) (node : SyntaxNode Atom) : Prop :=
  node.args.length ≤ IntTy.i64.max.toNat ∧
  ∀ slot ∈ node.args, ∀ value, slot = some value → syntaxValueValid heap value

theorem lockMacroNodeValid1 {Atom : Type} {heap : SyntaxHeap Atom}
    {head : String} {a : SyntaxValue Atom} (ha : syntaxValueValid heap a) :
    lockMacroNodeValid heap ⟨head, [some a]⟩ := by
  refine ⟨by change 1 ≤ IntTy.i64.max.toNat; decide, ?_⟩
  intro slot hslot value heq
  simp only [List.mem_singleton] at hslot
  cases hslot.symm.trans heq
  exact ha

theorem lockMacroNodeValid2 {Atom : Type} {heap : SyntaxHeap Atom}
    {head : String} {a b : SyntaxValue Atom}
    (ha : syntaxValueValid heap a) (hb : syntaxValueValid heap b) :
    lockMacroNodeValid heap ⟨head, [some a, some b]⟩ := by
  refine ⟨by change 2 ≤ IntTy.i64.max.toNat; decide, ?_⟩
  intro slot hslot value heq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
  rcases hslot with h | h
  · cases h.symm.trans heq; exact ha
  · cases h.symm.trans heq; exact hb

theorem lockIosMacroPreservesInputGraph_proven : LockIosMacroPreservesInputGraph := by
  intro Atom definitionFile stream expression before hv
  let extra := lockIosExtra definitionFile stream expression before.length
  let after := before ++ extra
  have hlenAfter : after.length = before.length + 12 := by
    simp only [after, extra, lockIosExtra, List.length_append, List.length_cons, List.length_nil]
  have hgrow : before.length ≤ after.length := by omega
  have hStream : syntaxValueValid after stream :=
    lockMacroValueValidLength hgrow stream (hv.2.1 stream (by simp))
  have hExpr : syntaxValueValid after expression :=
    lockMacroValueValidLength hgrow expression (hv.2.1 expression (by simp))
  have hRef : ∀ k, k < 12 → syntaxValueValid after (.exprRef (before.length + k)) := by
    intro k hk
    change before.length + k < after.length
    omega
  have hRef0 : syntaxValueValid after (.exprRef before.length) := by
    change before.length < after.length
    omega
  refine ⟨.exprRef (before.length + 11), after,
    lockIosMacroRun definitionFile stream expression before,
    List.take_left, hlenAfter, ?_, before.length + 11, rfl, by omega⟩
  refine ⟨by change 3 ≤ IntTy.u32.max.toNat; decide, ?_, ?_⟩
  · intro value hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hRef 11 (by omega)
    · exact hStream
    · exact hExpr
  · intro node hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · rcases hv.2.2 node hold with ⟨hn, hs⟩
      refine ⟨hn, ?_⟩
      intro slot hslot value heq
      exact lockMacroValueValidLength hgrow value (hs slot hslot value heq)
    · change lockMacroNodeValid after node
      simp only [extra, lockIosExtra, List.mem_cons, List.not_mem_nil, or_false] at hnew
      rcases hnew with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact lockMacroNodeValid1 hStream
      · exact lockMacroNodeValid2 hRef0 trivial
      · exact lockMacroNodeValid2 trivial (hRef 1 (by omega))
      · exact lockMacroNodeValid2 hRef0 trivial
      · exact lockMacroNodeValid2 trivial (hRef 3 (by omega))
      · exact lockMacroNodeValid2 trivial trivial
      · exact lockMacroNodeValid2 trivial (hRef 5 (by omega))
      · exact lockMacroNodeValid1 hExpr
      · exact lockMacroNodeValid2 trivial (hRef 7 (by omega))
      · exact lockMacroNodeValid2 trivial trivial
      · exact lockMacroNodeValid2 trivial (hRef 9 (by omega))
      · refine ⟨by change 12 ≤ IntTy.i64.max.toNat; decide, ?_⟩
        intro slot hslot value heq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
        rcases hslot with h | h | h | h | h | h | h | h | h | h | h | h
        · cases h.symm.trans heq; trivial
        · cases h.symm.trans heq; exact hRef 2 (by omega)
        · cases h.symm.trans heq; trivial
        · cases h.symm.trans heq; exact hRef 4 (by omega)
        · cases h.symm.trans heq; trivial
        · cases h.symm.trans heq; exact hRef 6 (by omega)
        · cases h.symm.trans heq; trivial
        · cases h.symm.trans heq; exact hRef 8 (by omega)
        · cases h.symm.trans heq; trivial
        · cases h.symm.trans heq; exact hRef 10 (by omega)
        · cases h.symm.trans heq; trivial
        · cases h.symm.trans heq; trivial

theorem getElemAppendOffset {α : Type} (before extra : List α) (k : Nat) :
    (before ++ extra)[before.length + k]? = extra[k]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]

theorem getElemAppendZero {α : Type} (before extra : List α) :
    (before ++ extra)[before.length]? = extra[0]? := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]

theorem lockMacroAtStep {Atom : Type} {heap : SyntaxHeap Atom}
    {handle index : Nat} {path : List Nat} {node : SyntaxNode Atom}
    {next finish : SyntaxValue Atom}
    (hnode : heap[handle]? = some node)
    (harg : node.args[index]? = some (some next))
    (hrest : LockMacroAt heap next path finish) :
    LockMacroAt heap (.exprRef handle) (index :: path) finish :=
  ⟨handle, node, next, rfl, hnode, harg, hrest⟩

theorem lockIosMacroSharesEscapedSyntax_proven : LockIosMacroSharesEscapedSyntax := by
  intro Atom definitionFile stream expression before _
  let extra := lockIosExtra definitionFile stream expression before.length
  let after := before ++ extra
  have h0 : after[before.length]? = some ⟨"escape", [some stream]⟩ :=
    getElemAppendZero before extra
  have h1 : after[before.length + 1]? =
      some ⟨".", [some (.exprRef before.length), some (.atom (.quotedSymbol "_dolock"))]⟩ :=
    getElemAppendOffset before extra 1
  have h2 : after[before.length + 2]? =
      some ⟨"=", [some (.symbol "l"), some (.exprRef (before.length + 1))]⟩ :=
    getElemAppendOffset before extra 2
  have h3 : after[before.length + 3]? =
      some ⟨".", [some (.exprRef before.length), some (.atom (.quotedSymbol "lock"))]⟩ :=
    getElemAppendOffset before extra 3
  have h4 : after[before.length + 4]? =
      some ⟨"=", [some (.symbol "temp"), some (.exprRef (before.length + 3))]⟩ :=
    getElemAppendOffset before extra 4
  have h7 : after[before.length + 7]? = some ⟨"escape", [some expression]⟩ :=
    getElemAppendOffset before extra 7
  have h8 : after[before.length + 8]? =
      some ⟨"=", [some (.symbol "val"), some (.exprRef (before.length + 7))]⟩ :=
    getElemAppendOffset before extra 8
  have h11 : after[before.length + 11]? =
      some ⟨"block", [
        some (.atom (.lineNumber (JInt.wrap .i64 40) definitionFile)), some (.exprRef (before.length + 2)),
        some (.atom (.lineNumber (JInt.wrap .i64 41) definitionFile)), some (.exprRef (before.length + 4)),
        some (.atom (.lineNumber (JInt.wrap .i64 42) definitionFile)), some (.exprRef (before.length + 6)),
        some (.atom (.lineNumber (JInt.wrap .i64 43) definitionFile)), some (.exprRef (before.length + 8)),
        some (.atom (.lineNumber (JInt.wrap .i64 44) definitionFile)), some (.exprRef (before.length + 10)),
        some (.atom (.lineNumber (JInt.wrap .i64 45) definitionFile)), some (.symbol "val")]⟩ :=
    getElemAppendOffset before extra 11
  refine ⟨.exprRef (before.length + 11), after, before.length, before.length + 7,
    lockIosMacroRun definitionFile stream expression before,
    Nat.le_refl _, by omega, by omega, h0, h7,
    lockMacroAtStep h11 rfl (lockMacroAtStep h2 rfl (lockMacroAtStep h1 rfl rfl)),
    lockMacroAtStep h11 rfl (lockMacroAtStep h4 rfl (lockMacroAtStep h3 rfl rfl)),
    lockMacroAtStep h11 rfl (lockMacroAtStep h8 rfl rfl)⟩


/-! ## `open(fname, mode; lock)` properties -/

def openModeAllLiterals : List Text :=
  [text "r", text "r+", text "w", text "w+", text "a", text "a+"]

def openModeFalseTrace {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) :
    List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result) :=
  prev.flatMap (fun lit => [.check mode lit, .compared lit (.inl false)])

theorem openModeFalseTrace_append_singleton {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) (lit : Text) :
    (openModeFalseTrace mode prev :
      List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) ++
      [.check mode lit, .compared lit (.inl false)] =
    openModeFalseTrace mode (prev ++ [lit]) := by
  simp only [openModeFalseTrace, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

inductive OpenModeOutcomeShape {World Name Mode OtherLock NotBool Message Result : Type}
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock) :
    Option (Except
      (Error × (World × List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)))
      (Result × (World × List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)))) → Prop where
  | div : OpenModeOutcomeShape name mode lock none
  | eqErr (prev rem : List Text) (lit : Text) (err : Error) (w : World) :
      prev ++ (lit :: rem) = openModeAllLiterals →
      OpenModeOutcomeShape name mode lock
        (some (.error (err, (w, openModeFalseTrace mode prev ++ [.check mode lit]))))
  | nonBool (prev rem : List Text) (lit : Text) (bad : NotBool) (w : World) :
      prev ++ (lit :: rem) = openModeAllLiterals →
      OpenModeOutcomeShape name mode lock
        (some (.error (.foreignError "TypeError" "",
          (w, openModeFalseTrace mode prev ++ [.check mode lit, .compared lit (.inr bad)]))))
  | openErr (prev rem : List Text) (lit : Text) (kw : OpenModeKeywordList OtherLock)
      (err : Error) (w : World) :
      prev ++ (lit :: rem) = openModeAllLiterals →
      OpenModeKeywordContract lock lit kw →
      OpenModeOutcomeShape name mode lock
        (some (.error (err, (w, openModeFalseTrace mode prev ++
          [.check mode lit, .compared lit (.inl true), .openCall name kw]))))
  | openOk (prev rem : List Text) (lit : Text) (kw : OpenModeKeywordList OtherLock)
      (res : Result) (w : World) :
      prev ++ (lit :: rem) = openModeAllLiterals →
      OpenModeKeywordContract lock lit kw →
      OpenModeOutcomeShape name mode lock
        (some (.ok (res, (w, openModeFalseTrace mode prev ++
          [.check mode lit, .compared lit (.inl true), .openCall name kw, .opened res]))))
  | interpErr (err : Error) (w : World) :
      OpenModeOutcomeShape name mode lock
        (some (.error (err, (w,
          openModeFalseTrace mode openModeAllLiterals ++
            [.interpolate (text "invalid open mode: ") mode]))))
  | makeErr (msg : Message) (err : Error) (w : World) :
      OpenModeOutcomeShape name mode lock
        (some (.error (err, (w,
          openModeFalseTrace mode openModeAllLiterals ++
            [.interpolate (text "invalid open mode: ") mode, .message msg, .makeError msg]))))
  | thrown (msg : Message) (constructed : Error) (w : World) :
      OpenModeOutcomeShape name mode lock
        (some (.error (constructed, (w,
          openModeFalseTrace mode openModeAllLiterals ++
            [.interpolate (text "invalid open mode: ") mode, .message msg,
             .makeError msg, .madeError constructed]))))

theorem openModeStepShape {World Name Mode OtherLock NotBool Message Result : Type}
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock)
    (prev rem : List Text) (lit : Text) (kw : OpenModeKeywordList OtherLock)
    (rest : M (World × List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) Result)
    (w : World)
    (hsplit : prev ++ (lit :: rem) = openModeAllLiterals)
    (hkw : OpenModeKeywordContract lock lit kw)
    (hrest : ∀ w1, OpenModeOutcomeShape name mode lock
      (rest (w1, openModeFalseTrace mode (prev ++ [lit])))) :
    OpenModeOutcomeShape name mode lock
      ((do
        if ← openModeCondition (← (openModeAuditOps ops).equals mode lit) then
          return ← (openModeAuditOps ops).openFile name kw
        rest) (w, openModeFalseTrace mode prev)) := by
  simp only [openModeAuditOps, openModeAuditEmit, openModeAuditLift,
    openModeCondition, JuliaLean.base.reduce.assertBool,
    streamBindRun, streamPureRun]
  cases ops.equals mode lit w with
  | none => exact .div
  | some outcome =>
    cases outcome with
    | error pair =>
      rcases pair with ⟨err, w1⟩
      exact .eqErr prev rem lit err w1 hsplit
    | ok pair =>
      rcases pair with ⟨ans, w1⟩
      cases ans with
      | inr bad =>
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact .nonBool prev rem lit bad w1 hsplit
      | inl b =>
        cases b with
        | false =>
          simp only [streamPureRun, Bool.false_eq_true, ↓reduceIte,
            List.append_assoc, List.cons_append, List.nil_append]
          rw [openModeFalseTrace_append_singleton]
          exact hrest w1
        | true =>
          simp only [openModeAuditEmit, openModeAuditLift, streamBindRun, streamPureRun,
            ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
          cases ops.openFile name kw w1 with
          | none => exact .div
          | some outcome =>
            cases outcome with
            | error pair =>
              rcases pair with ⟨err, w2⟩
              exact .openErr prev rem lit kw err w2 hsplit hkw
            | ok pair =>
              rcases pair with ⟨res, w2⟩
              simp only [List.append_assoc, List.cons_append, List.nil_append]
              exact .openOk prev rem lit kw res w2 hsplit hkw

theorem openModeTailShape {World Name Mode OtherLock NotBool Message Result : Type}
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock) (w : World) :
    OpenModeOutcomeShape name mode lock
      ((do
        let message ← (openModeAuditOps ops).interpolate (text "invalid open mode: ") mode
        throw (← (openModeAuditOps ops).argumentError message) :
        M (World × List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) Result)
        (w, openModeFalseTrace mode openModeAllLiterals)) := by
  simp only [openModeAuditOps, openModeAuditEmit, openModeAuditLift,
    streamBindRun, streamPureRun]
  cases ops.interpolate (text "invalid open mode: ") mode w with
  | none => exact .div
  | some outcome =>
    cases outcome with
    | error pair =>
      rcases pair with ⟨err, w1⟩
      exact .interpErr err w1
    | ok pair =>
      rcases pair with ⟨msg, w1⟩
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      cases ops.argumentError msg w1 with
      | none => exact .div
      | some outcome =>
        cases outcome with
        | error pair =>
          rcases pair with ⟨err, w2⟩
          exact .makeErr msg err w2
        | ok pair =>
          rcases pair with ⟨constructed, w2⟩
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          exact .thrown msg constructed w2

theorem openModeShape {World Name Mode OtherLock NotBool Message Result : Type}
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock) (world : World) :
    OpenModeOutcomeShape name mode lock
      (openMode (openModeAuditOps ops) name mode lock (world, [])) := by
  change OpenModeOutcomeShape name mode lock
    (openMode (openModeAuditOps ops) name mode lock (world, openModeFalseTrace mode []))
  unfold openMode
  apply openModeStepShape ops name mode lock []
    [text "r+", text "w", text "w+", text "a", text "a+"] (text "r")
    _ _ world rfl ⟨["read"], Or.inl ⟨rfl, rfl⟩, rfl⟩
  intro w1
  apply openModeStepShape ops name mode lock [text "r"]
    [text "w", text "w+", text "a", text "a+"] (text "r+")
    _ _ w1 rfl ⟨["read", "write"], Or.inr (Or.inl ⟨rfl, rfl⟩), rfl⟩
  intro w2
  apply openModeStepShape ops name mode lock [text "r", text "r+"]
    [text "w+", text "a", text "a+"] (text "w")
    _ _ w2 rfl ⟨["truncate"], Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), rfl⟩
  intro w3
  apply openModeStepShape ops name mode lock [text "r", text "r+", text "w"]
    [text "a", text "a+"] (text "w+")
    _ _ w3 rfl ⟨["truncate", "read"], Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), rfl⟩
  intro w4
  apply openModeStepShape ops name mode lock [text "r", text "r+", text "w", text "w+"]
    [text "a+"] (text "a")
    _ _ w4 rfl ⟨["append"], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))), rfl⟩
  intro w5
  apply openModeStepShape ops name mode lock [text "r", text "r+", text "w", text "w+", text "a"]
    [] (text "a+")
    _ _ w5 rfl ⟨["append", "read"], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))), rfl⟩
  intro w6
  exact openModeTailShape ops name mode lock w6

theorem openModeCheckedLiterals_falseTrace {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) :
    openModeCheckedLiterals
      (openModeFalseTrace mode prev :
        List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) = prev := by
  induction prev with
  | nil => rfl
  | cons lit rest ih =>
    simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
      openModeCheckedLiterals, List.filterMap_cons]
    exact congrArg (lit :: ·) ih

theorem check_mem_falseTrace {Name Mode OtherLock NotBool Message Result : Type}
    {mode checked : Mode} {literal : Text} {prev : List Text}
    (h : (OpenModeAuditEvent.check checked literal :
      OpenModeAuditEvent Name Mode OtherLock NotBool Message Result) ∈
      openModeFalseTrace mode prev) :
    checked = mode := by
  induction prev with
  | nil => cases h
  | cons lit rest ih =>
    simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
      List.mem_cons] at h
    rcases h with h | h | h
    · cases h; rfl
    · cases h
    · exact ih h

theorem openModeTestsInSourceOrder_proven : OpenModeTestsInSourceOrder := by
  intro World Name Mode OtherLock NotBool Message Result ops name mode lock world
  have hshape := openModeShape ops name mode lock world
  generalize openMode (openModeAuditOps ops) name mode lock (world, []) = out at hshape ⊢
  rcases hshape with
    _ | ⟨prev, rem, lit, err, w, hsplit⟩ |
    ⟨prev, rem, lit, bad, w, hsplit⟩ |
    ⟨prev, rem, lit, kw, err, w, hsplit, _⟩ |
    ⟨prev, rem, lit, kw, res, w, hsplit, _⟩ |
    ⟨err, w⟩ | ⟨msg, err, w⟩ | ⟨msg, constructed, w⟩
  · trivial
  all_goals
    dsimp only [OpenModeObserved]
    refine ⟨?_, ?_⟩
  · refine ⟨rem, ?_⟩
    simp only [openModeCheckedLiterals, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil]
    rw [← openModeCheckedLiterals, openModeCheckedLiterals_falseTrace, List.append_assoc]
    exact hsplit
  · intro checked literal hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact check_mem_falseTrace h1
    · simp only [List.mem_singleton] at h2; cases h2; rfl
  · refine ⟨rem, ?_⟩
    simp only [openModeCheckedLiterals, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil]
    rw [← openModeCheckedLiterals, openModeCheckedLiterals_falseTrace, List.append_assoc]
    exact hsplit
  · intro checked literal hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact check_mem_falseTrace h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 <;> cases h2 <;> rfl
  · refine ⟨rem, ?_⟩
    simp only [openModeCheckedLiterals, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil]
    rw [← openModeCheckedLiterals, openModeCheckedLiterals_falseTrace, List.append_assoc]
    exact hsplit
  · intro checked literal hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact check_mem_falseTrace h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 | h2 <;> cases h2 <;> rfl
  · refine ⟨rem, ?_⟩
    simp only [openModeCheckedLiterals, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil]
    rw [← openModeCheckedLiterals, openModeCheckedLiterals_falseTrace, List.append_assoc]
    exact hsplit
  · intro checked literal hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact check_mem_falseTrace h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 | h2 | h2 <;> cases h2 <;> rfl
  · refine ⟨[], ?_⟩
    simp only [openModeCheckedLiterals, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
    exact openModeCheckedLiterals_falseTrace mode openModeAllLiterals
  · intro checked literal hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact check_mem_falseTrace h1
    · simp only [List.mem_singleton] at h2; cases h2
  · refine ⟨[], ?_⟩
    simp only [openModeCheckedLiterals, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
    exact openModeCheckedLiterals_falseTrace mode openModeAllLiterals
  · intro checked literal hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact check_mem_falseTrace h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 | h2 <;> cases h2
  · refine ⟨[], ?_⟩
    simp only [openModeCheckedLiterals, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
    exact openModeCheckedLiterals_falseTrace mode openModeAllLiterals
  · intro checked literal hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact check_mem_falseTrace h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 | h2 | h2 <;> cases h2

theorem eq_of_not_mem_prefix {α : Type} {xs ys before after : List α} {e : α}
    (hnot : e ∉ xs)
    (heq : xs ++ ys = before ++ (e :: after)) :
    ∃ before', before = xs ++ before' ∧ ys = before' ++ (e :: after) := by
  induction xs generalizing before with
  | nil => exact ⟨before, rfl, heq⟩
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hnot
    cases before with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      exact False.elim (hnot.1 heq.1.symm)
    | cons b before =>
      simp only [List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, heq⟩
      obtain ⟨before', rfl, hys⟩ := ih hnot.2 heq
      exact ⟨before', rfl, hys⟩

theorem openCall_not_mem_falseTrace {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) (actualName : Name) (kw : OpenModeKeywordList OtherLock) :
    (OpenModeAuditEvent.openCall actualName kw :
      OpenModeAuditEvent Name Mode OtherLock NotBool Message Result) ∉
      openModeFalseTrace mode prev := by
  induction prev with
  | nil => simp [openModeFalseTrace]
  | cons lit rest ih =>
    simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
      List.mem_cons, not_or]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), ih⟩

theorem compared_inr_not_mem_falseTrace {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) (literal : Text) (bad : NotBool) :
    (OpenModeAuditEvent.compared literal (.inr bad) :
      OpenModeAuditEvent Name Mode OtherLock NotBool Message Result) ∉
      openModeFalseTrace mode prev := by
  induction prev with
  | nil => simp [openModeFalseTrace]
  | cons lit rest ih =>
    simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
      List.mem_cons, not_or]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), ih⟩

theorem interpolate_not_mem_falseTrace {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) (pfx : Text) (actualMode : Mode) :
    (OpenModeAuditEvent.interpolate pfx actualMode :
      OpenModeAuditEvent Name Mode OtherLock NotBool Message Result) ∉
      openModeFalseTrace mode prev := by
  induction prev with
  | nil => simp [openModeFalseTrace]
  | cons lit rest ih =>
    simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
      List.mem_cons, not_or]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), ih⟩

theorem makeError_not_mem_falseTrace {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) (msg : Message) :
    (OpenModeAuditEvent.makeError msg :
      OpenModeAuditEvent Name Mode OtherLock NotBool Message Result) ∉
      openModeFalseTrace mode prev := by
  induction prev with
  | nil => simp [openModeFalseTrace]
  | cons lit rest ih =>
    simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
      List.mem_cons, not_or]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), ih⟩

theorem madeError_not_mem_falseTrace {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) (err : Error) :
    (OpenModeAuditEvent.madeError err :
      OpenModeAuditEvent Name Mode OtherLock NotBool Message Result) ∉
      openModeFalseTrace mode prev := by
  induction prev with
  | nil => simp [openModeFalseTrace]
  | cons lit rest ih =>
    simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
      List.mem_cons, not_or]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), ih⟩

theorem openModeLastAnswer_append_compared {Name Mode OtherLock NotBool Message Result : Type}
    (xs : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result))
    (mode : Mode) (lit : Text) (ans : Bool ⊕ NotBool) :
    openModeLastAnswer (xs ++ [.check mode lit, .compared lit ans]) = some (lit, ans) := by
  unfold openModeLastAnswer
  rw [List.foldl_append]
  rfl

theorem openModeLastMessage_append_message {Name Mode OtherLock NotBool Message Result : Type}
    (xs : List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result))
    (pfx : Text) (mode : Mode) (msg : Message) :
    openModeLastMessage (xs ++ [.interpolate pfx mode, .message msg]) = some msg := by
  unfold openModeLastMessage
  rw [List.foldl_append]
  rfl

theorem openModeReturnedValues_openOk {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) (prev : List Text) (lit : Text) (name : Name)
    (kw : OpenModeKeywordList OtherLock) (res : Result) :
    openModeReturnedValues
      ((openModeFalseTrace mode prev :
        List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) ++
        [.check mode lit, .compared lit (.inl true), .openCall name kw, .opened res]) = [res] := by
  have hprev : openModeReturnedValues
      (openModeFalseTrace mode prev :
        List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) = [] := by
    induction prev with
    | nil => rfl
    | cons l rest ih =>
      simp only [openModeFalseTrace, List.flatMap_cons, List.cons_append, List.nil_append,
        openModeReturnedValues, List.filterMap_cons]
      exact ih
  simp only [openModeReturnedValues, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  unfold openModeReturnedValues at hprev
  rw [hprev]
  rfl

theorem openModeForwardsSelectedKeywordsAndResult_proven :
    OpenModeForwardsSelectedKeywordsAndResult := by
  intro World Name Mode OtherLock NotBool Message Result ops name mode lock world
  have hshape := openModeShape ops name mode lock world
  generalize openMode (openModeAuditOps ops) name mode lock (world, []) = out at hshape ⊢
  rcases hshape with
    _ | ⟨prev, rem, lit, err, w, _⟩ |
    ⟨prev, rem, lit, bad, w, _⟩ |
    ⟨prev, rem, lit, kw, err, w, _, hkw⟩ |
    ⟨prev, rem, lit, kw, res, w, _, hkw⟩ |
    ⟨err, w⟩ | ⟨msg, err, w⟩ | ⟨msg, constructed, w⟩
  · trivial
  · intro before after actualName keywords heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (openCall_not_mem_falseTrace mode prev actualName keywords) heq
    rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
  · intro before after actualName keywords heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (openCall_not_mem_falseTrace mode prev actualName keywords) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, before'⟩⟩ <;> simp at hys
  · intro before after actualName keywords heq
    obtain ⟨before', rfl, hys⟩ := eq_of_not_mem_prefix
      (openCall_not_mem_falseTrace mode prev actualName keywords) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
    rcases hys with ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
    refine ⟨rfl, ⟨lit, openModeLastAnswer_append_compared _ mode lit (.inl true), hkw⟩, Or.inl rfl⟩
  · refine ⟨?_, openModeReturnedValues_openOk mode prev lit name kw res⟩
    intro before after actualName keywords heq
    obtain ⟨before', rfl, hys⟩ := eq_of_not_mem_prefix
      (openCall_not_mem_falseTrace mode prev actualName keywords) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys
    rcases hys with ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
    refine ⟨rfl, ⟨lit, openModeLastAnswer_append_compared _ mode lit (.inl true), hkw⟩,
      Or.inr ⟨res, rfl⟩⟩
  · intro before after actualName keywords heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (openCall_not_mem_falseTrace mode openModeAllLiterals actualName keywords) heq
    rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
  · intro before after actualName keywords heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (openCall_not_mem_falseTrace mode openModeAllLiterals actualName keywords) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
  · intro before after actualName keywords heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (openCall_not_mem_falseTrace mode openModeAllLiterals actualName keywords) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys

theorem openModeRejectsNonBooleanEquality_proven : OpenModeRejectsNonBooleanEquality := by
  intro World Name Mode OtherLock NotBool Message Result ops name mode lock world
  have hshape := openModeShape ops name mode lock world
  generalize openMode (openModeAuditOps ops) name mode lock (world, []) = out at hshape ⊢
  rcases hshape with
    _ | ⟨prev, rem, lit, err, w, _⟩ |
    ⟨prev, rem, lit, bad0, w, _⟩ |
    ⟨prev, rem, lit, kw, err, w, _, _⟩ |
    ⟨prev, rem, lit, kw, res, w, _, _⟩ |
    ⟨err, w⟩ | ⟨msg, err, w⟩ | ⟨msg, constructed, w⟩
  · trivial
  · intro before after literal bad heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (compared_inr_not_mem_falseTrace mode prev literal bad) heq
    rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
  · intro before after literal bad heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (compared_inr_not_mem_falseTrace mode prev literal bad) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, before'⟩⟩ <;> simp at hys
    rcases hys with ⟨rfl, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · intro before after literal bad heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (compared_inr_not_mem_falseTrace mode prev literal bad) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
  · intro literal bad hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact compared_inr_not_mem_falseTrace mode prev literal bad h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 | h2 | h2 <;> cases h2
  · intro before after literal bad heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (compared_inr_not_mem_falseTrace mode openModeAllLiterals literal bad) heq
    rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
  · intro before after literal bad heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (compared_inr_not_mem_falseTrace mode openModeAllLiterals literal bad) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
  · intro before after literal bad heq
    obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
      (compared_inr_not_mem_falseTrace mode openModeAllLiterals literal bad) heq
    rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys

theorem openModeAnswers_allLiterals {Name Mode OtherLock NotBool Message Result : Type}
    (mode : Mode) :
    openModeAnswers
      (openModeFalseTrace mode openModeAllLiterals :
        List (OpenModeAuditEvent Name Mode OtherLock NotBool Message Result)) =
      openModeAllLiterals.map (fun literal => (literal, Sum.inl false)) := rfl

theorem openModePreservesInvalidMessageAndThrow_proven :
    OpenModePreservesInvalidMessageAndThrow := by
  intro World Name Mode OtherLock NotBool Message Result ops name mode lock world
  have hshape := openModeShape ops name mode lock world
  generalize openMode (openModeAuditOps ops) name mode lock (world, []) = out at hshape ⊢
  rcases hshape with
    _ | ⟨prev, rem, lit, err, w, _⟩ |
    ⟨prev, rem, lit, bad, w, _⟩ |
    ⟨prev, rem, lit, kw, err, w, _, _⟩ |
    ⟨prev, rem, lit, kw, res, w, _, _⟩ |
    ⟨err, w⟩ | ⟨msg, err, w⟩ | ⟨msg, constructed0, w⟩
  · trivial
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro before after pfx actualMode heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (interpolate_not_mem_falseTrace mode prev pfx actualMode) heq
      rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
    · intro before after message heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (makeError_not_mem_falseTrace mode prev message) heq
      rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
    · intro before after constructed heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (madeError_not_mem_falseTrace mode prev constructed) heq
      rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro before after pfx actualMode heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (interpolate_not_mem_falseTrace mode prev pfx actualMode) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, before'⟩⟩ <;> simp at hys
    · intro before after message heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (makeError_not_mem_falseTrace mode prev message) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, before'⟩⟩ <;> simp at hys
    · intro before after constructed heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (madeError_not_mem_falseTrace mode prev constructed) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, before'⟩⟩ <;> simp at hys
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro before after pfx actualMode heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (interpolate_not_mem_falseTrace mode prev pfx actualMode) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
    · intro before after message heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (makeError_not_mem_falseTrace mode prev message) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
    · intro before after constructed heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (madeError_not_mem_falseTrace mode prev constructed) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro before after pfx actualMode heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (interpolate_not_mem_falseTrace mode prev pfx actualMode) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys
    · intro before after message heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (makeError_not_mem_falseTrace mode prev message) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys
    · intro constructed hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact madeError_not_mem_falseTrace mode prev constructed h1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with h2 | h2 | h2 | h2 <;> cases h2
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro before after pfx actualMode heq
      obtain ⟨before', rfl, hys⟩ := eq_of_not_mem_prefix
        (interpolate_not_mem_falseTrace mode openModeAllLiterals pfx actualMode) heq
      rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
      rcases hys with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl, openModeAnswers_allLiterals mode⟩
    · intro before after message heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (makeError_not_mem_falseTrace mode openModeAllLiterals message) heq
      rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
    · intro before after constructed heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (madeError_not_mem_falseTrace mode openModeAllLiterals constructed) heq
      rcases before' with _ | ⟨b1, before'⟩ <;> simp at hys
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro before after pfx actualMode heq
      obtain ⟨before', rfl, hys⟩ := eq_of_not_mem_prefix
        (interpolate_not_mem_falseTrace mode openModeAllLiterals pfx actualMode) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
      rcases hys with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl, openModeAnswers_allLiterals mode⟩
    · intro before after message heq
      obtain ⟨before', rfl, hys⟩ := eq_of_not_mem_prefix
        (makeError_not_mem_falseTrace mode openModeAllLiterals message) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
      rcases hys with ⟨rfl, rfl, rfl, rfl⟩
      exact openModeLastMessage_append_message _ (text "invalid open mode: ") mode msg
    · intro before after constructed heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (madeError_not_mem_falseTrace mode openModeAllLiterals constructed) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, before'⟩⟩⟩ <;> simp at hys
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro before after pfx actualMode heq
      obtain ⟨before', rfl, hys⟩ := eq_of_not_mem_prefix
        (interpolate_not_mem_falseTrace mode openModeAllLiterals pfx actualMode) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys
      rcases hys with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl, openModeAnswers_allLiterals mode⟩
    · intro before after message heq
      obtain ⟨before', rfl, hys⟩ := eq_of_not_mem_prefix
        (makeError_not_mem_falseTrace mode openModeAllLiterals message) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys
      rcases hys with ⟨rfl, rfl, rfl, rfl⟩
      exact openModeLastMessage_append_message _ (text "invalid open mode: ") mode msg
    · intro before after constructed heq
      obtain ⟨before', _, hys⟩ := eq_of_not_mem_prefix
        (madeError_not_mem_falseTrace mode openModeAllLiterals constructed) heq
      rcases before' with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, before'⟩⟩⟩⟩ <;> simp at hys
      rcases hys with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩

end JuliaLean.Proofs.base.iostream.Models2Group18

namespace JuliaLean.Proofs.base.iostream.CoreIOStream

open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.iostream
open JuliaLean.Proofs.base.iostream.Models2Group18 (streamBindRun streamPureRun)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion)

/-- A failed conversion retains its exact world, and a returned non-String
is rejected before any selected open call. Source: base/iostream.jl:346. -/
def AbstractOpenChecksConversion : Prop :=
  ∀ (World Name Kw Result Other : Type)
    (convert : Name → M World (TypeAssertion Text Other))
    (openFile : Text → Kw → M World Result)
    (name : Name) (keywords : Kw) (before after : World)
    (failure : Error) (wrong : Other),
    (convert name before = some (.error (failure, after)) →
      openAbstractStringChecked convert openFile name keywords before =
        some (.error (failure, after))) ∧
    (convert name before = some (.ok (.rejected wrong, after)) →
      openAbstractStringChecked convert openFile name keywords before =
        some (.error (.showError .typeError, after)))

theorem abstractOpenChecksConversion_proven : AbstractOpenChecksConversion := by
  intro World Name Kw Result Other convert openFile name keywords before after failure wrong
  constructor <;> intro h
  · simp only [openAbstractStringChecked, streamBindRun, h]
  · simp only [openAbstractStringChecked, streamBindRun, h]
    rfl

def ResultOnly {World A : Type} (predicate : A → Prop)
    (outcome : Option (Except (Error × World) (A × World))) : Prop :=
  match outcome with
  | some (.ok (value, _)) => predicate value
  | _ => True

theorem bindResultOnly {World A B : Type} (predicate : B → Prop)
    (action : M World A) (next : A → M World B) (world : World)
    (h : ∀ value after, ResultOnly predicate (next value after)) :
    ResultOnly predicate ((action >>= next) world) := by
  simp only [streamBindRun]
  cases action world with
  | none => trivial
  | some outcome =>
    cases outcome with
    | error error => trivial
    | ok pair => exact h pair.1 pair.2

theorem lockIosResultOnly {World Stream Vector Lock A : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (stream : Stream) (body : M World A) (predicate : A → Prop)
    (hbody : ∀ world, ResultOnly predicate (body world)) (world : World) :
    ResultOnly predicate (lockIos access locks stream body world) := by
  unfold lockIos
  apply bindResultOnly
  intro fields after
  cases hlock : fields.dolock with
  | false =>
    simp only [hlock, Bool.false_eq_true, ↓reduceIte, streamBindRun]
    cases hb : body after with
    | none => trivial
    | some outcome =>
      cases outcome with
      | error error => trivial
      | ok pair => simpa only [hb, ResultOnly, streamPureRun] using hbody after
  | true =>
    simp only [hlock, ↓reduceIte]
    apply bindResultOnly
    intro _ afterLock
    simp only [streamBindRun]
    cases hb : body afterLock with
    | none => trivial
    | some outcome =>
      cases outcome with
      | error error => trivial
      | ok pair =>
        obtain ⟨value, afterBody⟩ := pair
        have hv : predicate value := by simpa only [hb, ResultOnly] using hbody afterLock
        dsimp only
        cases hu : locks.unlock fields.mutex afterBody with
        | none => trivial
        | some outcome =>
          cases outcome with
          | error error => trivial
          | ok pair => exact hv

/-- Locking and signed availability queries retain the actual C count,
including negative counts, without substitution or unsigned conversion.
Source: base/iostream.jl:429. -/
def BytesavailablePreservesSignedCount : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (count : CInt) (stream : Stream) (world : World),
    ResultOnly (fun result => result = count)
      (bytesavailable access locks
        { runtime with available := fun _ => pure count } stream world)

theorem bytesavailablePreservesSignedCount_proven :
    BytesavailablePreservesSignedCount := by
  intro World Stream Vector Lock access locks runtime count stream world
  unfold bytesavailable
  apply lockIosResultOnly
  intro before
  apply bindResultOnly
  intro pointer afterPointer
  rfl

/-- Every entry cancellation failure precedes allocation, foreign I/O, buffer
mutation and lock acquisition, and retains the precise failure world.
Source: base/iostream.jl:431-447,490-493,505-508,535-540,599-603,646-654. -/
def CancellationEntryFailureFirst : Prop :=
  ∀ (World Stream Vector Lock Token N : Type)
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector)
    (cancellation : JuliaLean.base.io.Cancellation World Token)
    (allocateAvailable : CInt → M World Vector)
    (readAll readSome : Stream → Vector → N → M World JuliaLean.base.io.I)
    (isTypemax : N → M World Bool)
    (allocateCount : Sum JuliaLean.base.io.I N → M World Vector)
    (readSelected : Stream → Vector → N → Bool → M World JuliaLean.base.io.I)
    (resize : Vector → JuliaLean.base.io.I → M World Unit)
    (stream out : Stream) (array : Vector) (count : N)
    (delim : JuliaLean.base.io.Byte) (keep all : Bool)
    (cancel : JuliaLean.base.io.CancelArg Token) (before after : World) (failure : Error),
    cancellation.check cancel before = some (.error (failure, after)) →
    readavailable access locks runtime cancellation allocateAvailable stream cancel before =
      some (.error (failure, after)) ∧
    readuntilByte access locks runtime cancellation stream delim keep cancel before =
      some (.error (failure, after)) ∧
    readline access locks runtime cancellation stream keep cancel before =
      some (.error (failure, after)) ∧
    copyuntilStream access locks runtime cancellation out stream delim keep cancel before =
      some (.error (failure, after)) ∧
    readbytes cancellation readAll readSome stream array count all cancel before =
      some (.error (failure, after)) ∧
    readCount cancellation isTypemax allocateCount readSelected resize
      stream count all cancel before = some (.error (failure, after))

theorem cancellationEntryFailureFirst_proven : CancellationEntryFailureFirst := by
  intro World Stream Vector Lock Token N access locks runtime cancellation allocateAvailable
    readAll readSome isTypemax allocateCount readSelected resize stream out array count
    delim keep all cancel before after failure h
  simp only [readavailable, readuntilByte, readline, copyuntilStream, readbytes,
    readCount, streamBindRun, h, and_self]

/-- Byte-read and peek interpret the C EOF sentinel identically after the
source lock scope has completed. Source: base/iostream.jl:449-455,658-664. -/
def ByteReadsRejectEOF : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) (before after : World),
    (lockIos access locks stream
      (do runtime.getc (← iosPointer access runtime stream)) before =
        some (.ok (cint (-1), after)) →
      readByte access locks runtime stream before = some (.error (.eofError, after))) ∧
    (lockIos access locks stream
      (do runtime.peekc (← iosPointer access runtime stream)) before =
        some (.ok (cint (-1), after)) →
      peekByte access locks runtime stream before = some (.error (.eofError, after)))

theorem byteReadsRejectEOF_proven : ByteReadsRejectEOF := by
  intro World Stream Vector Lock access locks runtime stream before after
  constructor <;> intro h
  · simp only [readByte, streamBindRun, h]
    rfl
  · simp only [peekByte, streamBindRun, h]
    rfl

/-- An incomplete unsafe read raises EOFError in the world left by the
completed read and unlock, without returning a partially initialized value.
Source: base/iostream.jl:477-483. -/
def UnsafeReadRejectsShortCount : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) (pointer : BytePointer)
    (requested actual : JuliaLean.base.io.U) (before after : World),
    actual.val ≠ requested.val →
    lockIos access locks stream
      (do runtime.readall (← iosPointer access runtime stream) pointer requested) before =
        some (.ok (actual, after)) →
    unsafeRead access locks runtime stream pointer requested before =
      some (.error (.eofError, after))

theorem unsafeReadRejectsShortCount_proven : UnsafeReadRejectsShortCount := by
  intro World Stream Vector Lock access locks runtime stream pointer requested actual
    before after hshort h
  simp only [unsafeRead, streamBindRun, h]
  simp [hshort]
  all_goals rfl

/-- Float reads preserve an integer-read exception and its exact world before
reinterpretation. Source: base/iostream.jl:472-474. -/
def FloatReadsPreserveErrors : Prop :=
  ∀ (World Stream : Type)
    (read16 : Stream → M World (JInt .i16))
    (read32 : Stream → M World (JInt .i32))
    (read64 : Stream → M World (JInt .i64))
    (stream : Stream) (before after : World) (failure : Error),
    (read16 stream before = some (.error (failure, after)) →
      readFloat16 read16 stream before = some (.error (failure, after))) ∧
    (read32 stream before = some (.error (failure, after)) →
      readFloat32 read32 stream before = some (.error (failure, after))) ∧
    (read64 stream before = some (.error (failure, after)) →
      readFloat64 read64 stream before = some (.error (failure, after)))

theorem floatReadsPreserveErrors_proven : FloatReadsPreserveErrors := by
  intro World Stream read16 read32 read64 stream before after failure
  constructor
  · intro h; simp only [readFloat16, streamBindRun, h]
  constructor
  · intro h; simp only [readFloat32, streamBindRun, h]
  · intro h; simp only [readFloat64, streamBindRun, h]

/-- A failed writable check prevents putc, locking and subsequent conversions,
and raises the exact documented ArgumentError in the check's resulting world.
Source: base/iostream.jl:411-414. -/
def WriteByteRejectsUnwritable : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) (byte : JuliaLean.base.io.Byte)
    (before after : World),
    iswritable access runtime stream before = some (.ok (false, after)) →
    writeByte access locks runtime stream byte before =
      some (.error (.jl (.argumentError "write failed, IOStream is not writeable"), after))

theorem writeByteRejectsUnwritable_proven : WriteByteRejectsUnwritable := by
  intro World Stream Vector Lock access locks runtime stream byte before after h
  simp only [writeByte, streamBindRun, h]
  rfl

theorem bindReturnedValueOnly {World A B : Type} (predicate : B → Prop)
    (effect : M World Unit) (value : A) (next : A → M World B) (world : World)
    (h : ∀ after, ResultOnly predicate (next value after)) :
    ResultOnly predicate (((do effect; pure value) >>= next) world) := by
  simp only [streamBindRun, streamPureRun]
  cases effect world with
  | none => trivial
  | some outcome =>
    cases outcome with
    | error error => trivial
    | ok pair => exact h pair.2

/-- Even arbitrary resizing return values cannot replace the allocated read
buffer. The allocator's world effects, all other callbacks and both source
allocation paths remain unrestricted. Source: base/iostream.jl:605-634. -/
def ReadAllRetainsAllocatedVector : Prop :=
  ∀ (World Stream Vector Lock : Type)
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector)
    (filesize position : Stream → M World JuliaLean.base.io.I)
    (isIOError : Error → Bool) (allocationEffects : JuliaLean.base.io.I → M World Unit)
    (readSelected : Stream → Vector → JuliaLean.base.io.I → M World JuliaLean.base.io.I)
    (resize : Vector → JuliaLean.base.io.I → M World Vector)
    (allocated : Vector) (stream : Stream) (world : World),
    ResultOnly (fun returned => returned = allocated)
      (readAll access locks runtime filesize position isIOError
        (fun n => do allocationEffects n; pure allocated) readSelected resize stream world)

theorem readAllRetainsAllocatedVector_proven : ReadAllRetainsAllocatedVector := by
  intro World Stream Vector Lock access locks runtime filesize position isIOError
    allocationEffects readSelected resize allocated stream world
  unfold readAll
  apply lockIosResultOnly
  intro before
  repeat' first
    | apply bindReturnedValueOnly; intro after
    | apply bindResultOnly; intro value after
    | split
    | rfl

end JuliaLean.Proofs.base.iostream.CoreIOStream

namespace JuliaLean.Proofs.base.iostream

open JuliaLean.Registry
open JuliaLean.base.iostream (openAbstractStringRuntime)

def OpenStringAssertion : Prop :=
  ∀ (W L Name Kw Result : Type) (ops : JuliaLean.base.boot.CoreOps W L)
    (convert : Name → JuliaLean.base.boot.CoreM W L (JuliaLean.base.expr.Value L))
    (openFile : JuliaLean.base.expr.Value L → Kw → JuliaLean.base.boot.CoreM W L Result)
    (name : Name) (keywords : Kw) (before after : W) (wrong : JuliaLean.base.expr.Value L),
    convert name before = some (.ok (wrong, after)) →
    ops.isa wrong (JuliaLean.base.boot.coreV ops "String") = false →
      openAbstractStringRuntime ops convert openFile name keywords before =
        some (.error (JuliaLean.base.boot.objV ops
          (.typeError (.symbol "typeassert") (JuliaLean.base.boot.strV ops "")
            (JuliaLean.base.boot.coreV ops "String") wrong), after))

theorem openStringAssertion_proven : OpenStringAssertion := by
  intro W L Name Kw Result ops convert openFile name keywords before after wrong converted rejected
  simp [openAbstractStringRuntime, JuliaLean.base.boot.typeassert,
    JuliaLean.base.boot.throwTypeError, JuliaLean.base.boot.throwObj,
    bind, pure, converted, rejected]
  rfl

def OpenStringEffects : Prop :=
  ∀ (W L Name Kw Result : Type) (ops : JuliaLean.base.boot.CoreOps W L)
    (convert : Name → JuliaLean.base.boot.CoreM W L (JuliaLean.base.expr.Value L))
    (openFile : JuliaLean.base.expr.Value L → Kw → JuliaLean.base.boot.CoreM W L Result)
    (name : Name) (keywords : Kw) (before after : W)
    (filename failure : JuliaLean.base.expr.Value L),
    (convert name before = none →
      openAbstractStringRuntime ops convert openFile name keywords before = none) ∧
    (convert name before = some (.error (failure, after)) →
      openAbstractStringRuntime ops convert openFile name keywords before =
        some (.error (failure, after))) ∧
    (convert name before = some (.ok (filename, after)) →
      ops.isa filename (JuliaLean.base.boot.coreV ops "String") = true →
      openAbstractStringRuntime ops convert openFile name keywords before =
        openFile filename keywords after)

theorem openStringEffects_proven : OpenStringEffects := by
  intro W L Name Kw Result ops convert openFile name keywords before after filename failure
  constructor
  · intro h
    simp [openAbstractStringRuntime, bind, h]
  constructor
  · intro h
    simp [openAbstractStringRuntime, bind, h]
  · intro h accepted
    simp [openAbstractStringRuntime, JuliaLean.base.boot.typeassert, bind, pure, h, accepted]

namespace ExactConstructor

open JuliaLean JuliaLean.base.io
open JuliaLean.base.iostream
open JuliaLean.base.iostream.Models2Group18
open JuliaLean.Proofs.base.iostream.Models2Group18 (streamBindRun)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion)

def BadNamePayloadAfterLock : Prop :=
  ∀ (World L Name Stream Vector Lock : Type)
    (encoding : JuliaLean.base.boot.CoreOps World L)
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name (JuliaLean.base.expr.Value L))
    (name : Name) (buffer : Vector) (wrong : JuliaLean.base.expr.Value L)
    (pointer : BytePointer) (mutex : Lock)
    (before afterPointer afterName afterLock : World),
    vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) →
    names.convertString name afterPointer = some (.ok (.rejected wrong, afterName)) →
    JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime locks) afterName =
      some (.ok (mutex, afterLock)) →
    (newStreamWithBufferExact encoding access vectors locks names (.inr name) buffer).run before =
      some (.ok (.error (.typeError (.symbol "new")
        (JuliaLean.base.boot.strV encoding "") (JuliaLean.base.boot.coreV encoding "String") wrong), afterLock))

theorem badNamePayloadAfterLock_proven : BadNamePayloadAfterLock := by
  intro World L Name Stream Vector Lock encoding access vectors locks names name buffer
    wrong pointer mutex before afterPointer afterName afterLock hp hn hl
  simp only [newStreamWithBufferExact, ExceptT.run, ExceptT.mk, sourceNewStreamWithBuffer,
    streamBindRun, hp, hn, hl]
  rfl

def ConversionFailurePrecedesTypeError : Prop :=
  ∀ (World L Name Stream Vector Lock : Type)
    (encoding : JuliaLean.base.boot.CoreOps World L)
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name (JuliaLean.base.expr.Value L))
    (name : Name) (buffer : Vector) (pointer : BytePointer)
    (before afterPointer afterName : World) (failure : Error),
    vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) →
    names.convertString name afterPointer = some (.error (failure, afterName)) →
    (newStreamWithBufferExact encoding access vectors locks names (.inr name) buffer).run before =
      some (.error (failure, afterName))

theorem conversionFailurePrecedesTypeError_proven : ConversionFailurePrecedesTypeError := by
  intro World L Name Stream Vector Lock encoding access vectors locks names name buffer
    pointer before afterPointer afterName failure hp hn
  simp only [newStreamWithBufferExact, ExceptT.run, ExceptT.mk, sourceNewStreamWithBuffer,
    streamBindRun, hp, hn]

def LockFailurePrecedesTypeError : Prop :=
  ∀ (World L Name Stream Vector Lock : Type)
    (encoding : JuliaLean.base.boot.CoreOps World L)
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name (JuliaLean.base.expr.Value L))
    (name : Name) (buffer : Vector) (wrong : JuliaLean.base.expr.Value L)
    (pointer : BytePointer) (before afterPointer afterName afterLock : World) (failure : Error),
    vectorPointer vectors buffer before = some (.ok (pointer, afterPointer)) →
    names.convertString name afterPointer = some (.ok (.rejected wrong, afterName)) →
    JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime locks) afterName =
      some (.error (failure, afterLock)) →
    (newStreamWithBufferExact encoding access vectors locks names (.inr name) buffer).run before =
      some (.error (failure, afterLock))

theorem lockFailurePrecedesTypeError_proven : LockFailurePrecedesTypeError := by
  intro World L Name Stream Vector Lock encoding access vectors locks names name buffer
    wrong pointer before afterPointer afterName afterLock failure hp hn hl
  simp only [newStreamWithBufferExact, ExceptT.run, ExceptT.mk, sourceNewStreamWithBuffer,
    streamBindRun, hp, hn, hl]

end ExactConstructor

def entriesModels2Group18 : List Entry := [
  { id := "iostream-inner-exact-typeerror", juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "After a name conversion returns a non-String value and lock construction succeeds, the constructor raises TypeError(:new, empty context, String, actual converted value) with the lock's final world.",
    source := "base/iostream.jl:21; src/datatype.c:1707-1723",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.ExactConstructor.BadNamePayloadAfterLock,
    thm := some ``JuliaLean.Proofs.base.iostream.ExactConstructor.badNamePayloadAfterLock_proven },
  { id := "iostream-inner-exact-conversion-failure", juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "An actual name-conversion exception retains its exact error and world and precedes the constructor's own TypeError.",
    source := "base/iostream.jl:21; src/julia-syntax.scm:795-806,3870-3893",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.ExactConstructor.ConversionFailurePrecedesTypeError,
    thm := some ``JuliaLean.Proofs.base.iostream.ExactConstructor.conversionFailurePrecedesTypeError_proven },
  { id := "iostream-inner-exact-lock-failure", juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "After a non-String name-conversion result, an actual lock-construction exception retains its exact error and world and precedes the constructor's own TypeError.",
    source := "base/iostream.jl:21; src/julia-syntax.scm:795-806,3870-3893",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.ExactConstructor.LockFailurePrecedesTypeError,
    thm := some ``JuliaLean.Proofs.base.iostream.ExactConstructor.lockFailurePrecedesTypeError_proven },
  { id := "iostream-read-all-buffer-identity",
    juliaFile := "base/iostream.jl",
    juliaFns := ["read(s::IOStream)"],
    statement := "Both read-all allocation paths return the allocated buffer, independently of resizing return values and all primitive world effects.",
    source := "base/iostream.jl:605-634",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.ReadAllRetainsAllocatedVector,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.readAllRetainsAllocatedVector_proven },
  { id := "iostream-cancellation-entry-failure",
    juliaFile := "base/iostream.jl",
    juliaFns := ["readavailable", "readuntil(::IOStream, ::UInt8)", "readline(::IOStream)",
      "copyuntil(::IOStream, ::IOStream, ::UInt8)", "readbytes!", "read(::IOStream, ::Integer)"],
    statement := "Cancellation failure precedes allocation, foreign I/O, mutation and locking, retaining its exact failure world.",
    source := "base/iostream.jl:431-447,490-493,505-508,535-540,599-603,646-654",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.CancellationEntryFailureFirst,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.cancellationEntryFailureFirst_proven },
  { id := "iostream-byte-read-peek-eof",
    juliaFile := "base/iostream.jl",
    juliaFns := ["read(::IOStream, ::Type{UInt8})", "peek(::IOStream, ::Type{UInt8})"],
    statement := "Byte read and peek raise EOFError for the C EOF sentinel after the lock scope, preserving its resulting world.",
    source := "base/iostream.jl:449-455,658-664",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.ByteReadsRejectEOF,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.byteReadsRejectEOF_proven },
  { id := "iostream-unsafe-read-short-count",
    juliaFile := "base/iostream.jl",
    juliaFns := ["unsafe_read(::IOStream, ::Ptr{UInt8}, ::UInt)"],
    statement := "Unsafe read raises EOFError whenever the completed C read returns fewer bytes than requested.",
    source := "base/iostream.jl:477-483",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.UnsafeReadRejectsShortCount,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.unsafeReadRejectsShortCount_proven },
  { id := "iostream-float-read-error-state",
    juliaFile := "base/iostream.jl",
    juliaFns := ["read(::IOStream, ::Type{Float16})", "read(::IOStream, ::Type{Float32})",
      "read(::IOStream, ::Type{Float64})"],
    statement := "All three floating-point reads propagate integer-read errors and their exact resulting worlds before reinterpretation.",
    source := "base/iostream.jl:472-474",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.FloatReadsPreserveErrors,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.floatReadsPreserveErrors_proven },
  { id := "iostream-byte-write-unwritable",
    juliaFile := "base/iostream.jl",
    juliaFns := ["write(::IOStream, ::UInt8)"],
    statement := "A failed writable check raises the exact ArgumentError before putc, locking or subsequent conversion.",
    source := "base/iostream.jl:411-414",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.WriteByteRejectsUnwritable,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.writeByteRejectsUnwritable_proven },
  { id := "iostream-abstract-open-conversion-check",
    juliaFile := "base/iostream.jl",
    juliaFns := ["open(fname::AbstractString; kwargs...)"],
    statement := "Conversion errors retain their exact mutated world, and a returned non-String raises TypeError before opening.",
    source := "base/iostream.jl:346",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.AbstractOpenChecksConversion,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.abstractOpenChecksConversion_proven },
  { id := "iostream-available-signed-count",
    juliaFile := "base/iostream.jl",
    juliaFns := ["bytesavailable(s::IOStream)"],
    statement := "Successful availability queries retain the exact signed C count, including negative results.",
    source := "base/iostream.jl:429",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.CoreIOStream.BytesavailablePreservesSignedCount,
    thm := some ``JuliaLean.Proofs.base.iostream.CoreIOStream.bytesavailablePreservesSignedCount_proven },
  { id := "iostream-open-string-assertion", juliaFile := "base/iostream.jl",
    juliaFns := ["open(fname::AbstractString; kwargs...)"],
    statement := "An invalid String conversion result raises TypeError(:typeassert, \"\", String, actual), retains conversion effects, and never calls open.",
    source := "base/iostream.jl:346; base/boot.jl:524-535 (type assertion error payload)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.OpenStringAssertion,
    thm := some ``JuliaLean.Proofs.base.iostream.openStringAssertion_proven },
  { id := "iostream-open-string-effects", juliaFile := "base/iostream.jl",
    juliaFns := ["open(fname::AbstractString; kwargs...)"],
    statement := "String conversion divergence and exceptions propagate unchanged; a successful String result reaches open with the original keywords and resulting world and preserves its complete outcome.",
    source := "base/iostream.jl:346 (conversion order and selected outcome)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.OpenStringEffects,
    thm := some ``JuliaLean.Proofs.base.iostream.openStringEffects_proven },
  { id := "iostream-allocation-dimensions",
    juliaFile := "base/boot.jl",
    juliaFns := ["Array{T,1}(::UndefInitializer, m::Int) (T=UInt8 dependency)"],
    statement := "The UInt8 allocation dependency rejects every negative or excessive native dimension before any raw allocation or mutation, and the zeros composition preserves that error.",
    source := "base/iostream.jl:25; base/boot.jl:821-824; src/genericmemory.c:55-73 (allocation invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.ByteInvalidDimensionsRejected,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.byteInvalidDimensionsRejected_proven },
  { id := "iostream-fill-identity",
    juliaFile := "base/array.jl",
    juliaFns := ["fill!(a::Array{UInt8}, x) (dependency)"],
    statement := "The byte-fill dependency returns the original vector identity on every successful execution, preserving the alias used by the constructor.",
    source := "base/iostream.jl:25-26; base/array.jl:473-480 (in-place identity invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.ByteFillPreservesIdentity,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.byteFillPreservesIdentity_proven },
  { id := "iostream-zeros-fill-arguments",
    juliaFile := "base/array.jl",
    juliaFns := ["zeros(UInt8, dims::Tuple{Int}) (dependency)"],
    statement := "Every reached zero-fill C call uses byte zero and the actual allocated vector reference and observed length; successful zeros issues exactly one fill and returns the allocated identity.",
    source := "base/iostream.jl:25; base/array.jl:473-480,631-653; base/boot.jl:821-824 (allocation/fill invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.ByteZerosZeroFillArguments,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.byteZerosZeroFillArguments_proven },
  { id := "iostream-constructor-finalization-disabled",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, finalize::Bool)"],
    statement := "With finalize=false, the constructor's full result, errors, mutations and termination are independent of every finalizer operation, for all custom constructor dispatches.",
    source := "base/iostream.jl:24-31 (finalization flag invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FinalizationDisabledIgnoresGC,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.finalizationDisabledIgnoresGC_proven },
  { id := "iostream-constructor-result-identity",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, finalize::Bool)"],
    statement := "Successful construction returns the exact result selected by the name/buffer constructor, including custom result types, despite any finalizer effects.",
    source := "base/iostream.jl:26-30 (return identity invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FinalizedConstructorPreservesResult,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.finalizedConstructorPreservesResult_proven },
  { id := "iostream-default-finalization",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString)"],
    statement := "The default name constructor invokes the selected name/Bool constructor exactly once with the original name and finalization enabled.",
    source := "base/iostream.jl:32 (default finalization invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.DefaultConstructorRequestsFinalization,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.defaultConstructorRequestsFinalization_proven },
  { id := "iostream-unsafe-convert-current-address",
    juliaFile := "base/iostream.jl",
    juliaFns := ["unsafe_convert(T::Type{Ptr{Cvoid}}, s::IOStream)"],
    statement := "Stream pointer conversion returns the current UInt8 memory-reference address and preserves state, independently of the cached handle.",
    source := "base/iostream.jl:34; base/pointer.jl:75-88 (UInt8 storage invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.UnsafeConvertUsesCurrentBackingAddress,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.unsafeConvertUsesCurrentBackingAddress_proven },
  { id := "iostream-shared-buffer-pointer",
    juliaFile := "base/iostream.jl",
    juliaFns := ["unsafe_convert(T::Type{Ptr{Cvoid}}, s::IOStream)"],
    statement := "Streams sharing one vector have the same pointer-conversion outcome regardless of their cached handles and other fields.",
    source := "base/iostream.jl:34 (buffer alias invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.SharedBufferHasSharedPointer,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.sharedBufferHasSharedPointer_proven },
  { id := "iostream-show-name-dispatch",
    juliaFile := "base/iostream.jl",
    juliaFns := ["show(io::IO, s::IOStream)"],
    statement := "Show invokes arbitrary selected print once with the original output and stream name enclosed in IOStream(...), preserving errors and state effects.",
    source := "base/iostream.jl:35 (display and dispatch invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.ShowPreservesNameAndDispatch,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.showPreservesNameAndDispatch_proven },
  { id := "iostream-show-result",
    juliaFile := "base/iostream.jl",
    juliaFns := ["show(io::IO, s::IOStream)"],
    statement := "Show preserves the arbitrary return value and post-call world of a selected custom print method.",
    source := "base/iostream.jl:35 (custom IO result forwarding invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.ShowForwardsArbitraryResult,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.showForwardsArbitraryResult_proven },
  { id := "iostream-lock-macro-input-graph",
    juliaFile := "base/iostream.jl",
    juliaFns := ["@_lock_ios(s, expr)"],
    statement := "Macro expansion preserves every pre-existing syntax node and slot, adds twelve fresh expression nodes, and returns a valid new graph root.",
    source := "base/iostream.jl:37-47 (syntax graph preservation invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.LockIosMacroPreservesInputGraph,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.lockIosMacroPreservesInputGraph_proven },
  { id := "iostream-lock-macro-sharing",
    juliaFile := "base/iostream.jl",
    juliaFns := ["@_lock_ios(s, expr)"],
    statement := "The two stream field expressions share one escaped input node; the body has a distinct escape preserving the original expression identity.",
    source := "base/iostream.jl:38-44 (macro hygiene and sharing invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.LockIosMacroSharesEscapedSyntax,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.lockIosMacroSharesEscapedSyntax_proven },
  { id := "iostream-descriptor-exact",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fd(s::IOStream)"],
    statement := "Successful fd returns the exact descriptor reported by C, with checked Int32 narrowing and no silent wrap.",
    source := "base/iostream.jl:49-74; base/libc.jl:34-35",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdReturnedDescriptorExact,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdReturnedDescriptorExact_proven },

  { id := "iostream-seekstart-origin",
    juliaFile := "base/iostream.jl",
    juliaFns := ["seekstart(s::IO)"],
    statement := "Seekstart makes exactly one selected seek request for the original stream at absolute byte offset zero.",
    source := "base/iostream.jl:165-185 (seek-to-beginning contract)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.SeekstartRequestsOrigin,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.seekstartRequestsOrigin_proven },
  { id := "iostream-seekstart-custom-outcomes",
    juliaFile := "base/iostream.jl",
    juliaFns := ["seekstart(s::IO)"],
    statement := "Seekstart preserves arbitrary custom seek return values, errors and resulting worlds.",
    source := "base/iostream.jl:185 (custom IO forwarding invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.SeekstartForwardsCustomOutcomes,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.seekstartForwardsCustomOutcomes_proven },
  { id := "iostream-custom-finalizer-dispatch",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, finalize::Bool)"],
    statement := "A selected custom finalizer is invoked exactly once with Base.close and the actual constructed result, preserving its errors and state effects while ignoring its arbitrary return value.",
    source := "base/iostream.jl:26-30 (custom finalizer dispatch invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.CustomFinalizerReceivesCloseAndResult,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.customFinalizerReceivesCloseAndResult_proven },
  { id := "iostream-query-snapshot",
    juliaFile := "base/iostream.jl",
    juliaFns := ["isopen(s::IOStream)", "iswritable(s::IOStream)", "isreadable(s::IOStream)"],
    statement := "Queries agree with the physical descriptor and independent permission flags and preserve the entire world.",
    source := "base/iostream.jl:78-88,104-106; src/support/ios.c:723-725",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.StreamQueriesDescribeSnapshot,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.streamQueriesDescribeSnapshot_proven },
  { id := "iostream-closed-capability-isolation",
    juliaFile := "base/iostream.jl",
    juliaFns := ["iswritable(s::IOStream)", "isreadable(s::IOStream)"],
    statement := "Closed queries suppress all later permission primitives, including their arbitrary errors and world effects.",
    source := "base/iostream.jl:104-106",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.ClosedQueriesIgnoreCapabilities,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.closedQueriesIgnoreCapabilities_proven },
  { id := "iostream-query-error-state",
    juliaFile := "base/iostream.jl",
    juliaFns := ["isopen(s::IOStream)", "iswritable(s::IOStream)", "isreadable(s::IOStream)"],
    statement := "Open-query failure propagates unchanged through all three public queries, including the primitive failure world.",
    source := "base/iostream.jl:88,104-106",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.StreamQueriesPreservePrimitiveFailure,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.streamQueriesPreservePrimitiveFailure_proven },
  { id := "iostream-closewrite-world",
    juliaFile := "base/iostream.jl",
    juliaFns := ["closewrite(s::IOStream)"],
    statement := "Closewrite returns nothing while preserving the complete world for every stream.",
    source := "base/iostream.jl:95",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.ClosewritePreservesWholeWorld,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.closewritePreservesWholeWorld_proven },
  { id := "iostream-eof-observed-end",
    juliaFile := "base/iostream.jl",
    juliaFns := ["_eof_nolock(s::IOStream)"],
    statement := "The no-lock EOF query agrees with an independently observed input-end flag under arbitrary primitive effects.",
    source := "base/iostream.jl:78-88,262",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.EofReflectsObservedEnd,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.eofReflectsObservedEnd_proven },
  { id := "iostream-eof-open-independence",
    juliaFile := "base/iostream.jl",
    juliaFns := ["_eof_nolock(s::IOStream)"],
    statement := "The no-lock EOF query is independent of the descriptor open-query operation, including errors, mutations and divergence.",
    source := "base/iostream.jl:78-88,262",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.EofIndependentOfOpenQuery,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.eofIndependentOfOpenQuery_proven },
  { id := "iostream-open-mode-order",
    juliaFile := "base/iostream.jl",
    juliaFns := ["open(fname::AbstractString, mode::AbstractString; lock = true)"],
    statement := "Mode comparisons receive the original mode and a prefix of the six source literals, preserving short circuit order for arbitrary custom equality.",
    source := "base/iostream.jl:399",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.OpenModeTestsInSourceOrder,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.openModeTestsInSourceOrder_proven },
  { id := "iostream-open-mode-keywords-result",
    juliaFile := "base/iostream.jl",
    juliaFns := ["open(fname::AbstractString, mode::AbstractString; lock = true)"],
    statement := "Selected open receives the untouched filename and lock plus the exact ordered keyword tuple, and its arbitrary result is returned unchanged.",
    source := "base/iostream.jl:399",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.OpenModeForwardsSelectedKeywordsAndResult,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.openModeForwardsSelectedKeywordsAndResult_proven },
  { id := "iostream-open-mode-bool-check",
    juliaFile := "base/iostream.jl",
    juliaFns := ["open(fname::AbstractString, mode::AbstractString; lock = true)"],
    statement := "A non-Bool comparison result raises TypeError immediately before any later selected operation.",
    source := "base/iostream.jl:399",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.OpenModeRejectsNonBooleanEquality,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.openModeRejectsNonBooleanEquality_proven },
  { id := "iostream-open-mode-invalid-throw",
    juliaFile := "base/iostream.jl",
    juliaFns := ["open(fname::AbstractString, mode::AbstractString; lock = true)"],
    statement := "Invalid-mode interpolation and exception construction retain their selected arguments, effects and arbitrary results; the outer throw uses the exact constructed value.",
    source := "base/iostream.jl:399",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.OpenModePreservesInvalidMessageAndThrow,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.openModePreservesInvalidMessageAndThrow_proven },
  { id := "iostream-fdio-constructed-identity",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fdio(name::AbstractString, fd::Integer, own::Bool=false)"],
    statement := "Successful named fdio preserves the arbitrary object returned by the selected constructor, including non-IOStream results.",
    source := "base/iostream.jl:281",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdioNamedPreservesConstructedIdentity,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdioNamedPreservesConstructedIdentity_proven },
  { id := "iostream-fdio-constructor-failure",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fdio(name::AbstractString, fd::Integer, own::Bool=false)"],
    statement := "Constructor failure wins before property lookup, conversions, GC preservation or C calls and retains its exact mutated world.",
    source := "base/iostream.jl:281",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdioNamedConstructorFailureFirst,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdioNamedConstructorFailureFirst_proven },
  { id := "iostream-fdio-conversion-stages",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fdio(name::AbstractString, fd::Integer, own::Bool=false)"],
    statement := "All cconvert calls precede unsafe_convert; a failing Clong cconvert wins over pointer unsafe conversion and every subsequent operation.",
    source := "base/iostream.jl:281",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdioAllCconvertBeforeUnsafe,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdioAllCconvertBeforeUnsafe_proven },
  { id := "iostream-fdio-abi-assertion",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fdio(name::AbstractString, fd::Integer, own::Bool=false)"],
    statement := "The ABI assertion preserves accepted values and raises TypeError for wrong-type conversion results at the source point.",
    source := "base/iostream.jl:281",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdioABITypeAssertion,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdioABITypeAssertion_proven },
  { id := "iostream-fdio-default-protocol",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fdio(fd::Integer, own::Bool=false)"],
    statement := "Unnamed fdio formats the descriptor label, forwards the actual custom name and unchanged descriptor/ownership, and returns the selected fdio result.",
    source := "base/iostream.jl:287",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdioDefaultArgumentProtocol,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdioDefaultArgumentProtocol_proven },
  { id := "iostream-fdio-string-failure",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fdio(fd::Integer, own::Bool=false)"],
    statement := "A descriptor-formatting failure retains its exact mutated world and precedes named fdio dispatch.",
    source := "base/iostream.jl:287",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdioDefaultStringFailureFirst,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdioDefaultStringFailureFirst_proven },












  { id := "iostream-fdio-unsafe-before-abi",
    juliaFile := "base/iostream.jl",
    juliaFns := ["fdio(name::AbstractString, fd::Integer, own::Bool=false)"],
    statement := "A wrong-type pointer conversion result still permits the later unsafe Clong conversion to run, mutate, throw or diverge before the foreign-call ABI check.",
    source := "base/iostream.jl:281-285; src/julia-syntax.scm:1069-1106,4861-4897,4973-4982 (conversion and ABI failure order)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.FdioAllUnsafeBeforeABI,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.fdioAllUnsafeBeforeABI_proven },
  { id := "iostream-inner-buffer-state",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "Every successful allocation request retains the original vector identity, mark minus one and enabled locking over the full input and runtime domain.",
    source := "base/iostream.jl:13-22; src/julia-syntax.scm:795-806,826-830,3870-3893,4872-4897; src/datatype.c:1707-1723 (initialization and implicit conversion)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.InnerConstructorRetainsBufferAndInitialState,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.innerConstructorRetainsBufferAndInitialState_proven },
  { id := "iostream-inner-string-bypass",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "For every already-String name, the complete constructor outcome is independent of non-String conversion dispatch.",
    source := "base/iostream.jl:13-22; src/julia-syntax.scm:795-806,826-830,3870-3893,4872-4897; src/datatype.c:1707-1723 (initialization and implicit conversion)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.InnerStringNameBypassesConversion,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.innerStringNameBypassesConversion_proven },
  { id := "iostream-inner-string-bytes",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "Every successful already-String allocation request preserves the exact name bytes, including invalid UTF-8.",
    source := "base/iostream.jl:13-22; src/julia-syntax.scm:795-806,826-830,3870-3893,4872-4897; src/datatype.c:1707-1723 (initialization and implicit conversion)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.InnerStringNamePreservesBytes,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.innerStringNamePreservesBytes_proven },
  { id := "iostream-inner-converted-bytes",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "Successful custom conversion bytes are retained exactly in a successful allocation request, without a conversion correctness law.",
    source := "base/iostream.jl:13-22; src/julia-syntax.scm:795-806,826-830,3870-3893,4872-4897; src/datatype.c:1707-1723 (initialization and implicit conversion)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.InnerConvertedNamePreservesBytes,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.innerConvertedNamePreservesBytes_proven },
  { id := "iostream-inner-conversion-before-lock",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "An actual name-conversion error propagates with its final world before lock construction or stream allocation.",
    source := "base/iostream.jl:13-22; src/julia-syntax.scm:795-806,826-830,3870-3893,4872-4897; src/datatype.c:1707-1723 (initialization and implicit conversion)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.InnerConversionFailurePrecedesLockConstruction,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.innerConversionFailurePrecedesLockConstruction_proven },
  { id := "iostream-inner-lock-error-before-typeerror",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "After a non-String conversion result, an actual lock-constructor error precedes the pending final-new TypeError.",
    source := "base/iostream.jl:13-22; src/julia-syntax.scm:795-806,826-830,3870-3893,4872-4897; src/datatype.c:1707-1723 (initialization and implicit conversion)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.InnerLockFailurePrecedesReturnedNameTypeError,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.innerLockFailurePrecedesReturnedNameTypeError_proven },
  { id := "iostream-inner-typeerror-lock-effects",
    juliaFile := "base/iostream.jl",
    juliaFns := ["IOStream(name::AbstractString, buf::Vector{UInt8})"],
    statement := "A non-String conversion result is rejected only after lock construction, retaining its world and skipping stream allocation.",
    source := "base/iostream.jl:13-22; src/julia-syntax.scm:795-806,826-830,3870-3893,4872-4897; src/datatype.c:1707-1723 (initialization and implicit conversion)",
    status := .proven, prop := ``JuliaLean.Proofs.base.iostream.Models2Group18.InnerReturnedNameTypeErrorKeepsLockEffects,
    thm := some ``JuliaLean.Proofs.base.iostream.Models2Group18.innerReturnedNameTypeErrorKeepsLockEffects_proven },
























]

end JuliaLean.Proofs.base.iostream
