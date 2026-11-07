import JuliaLean.base.stacktraces
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.stacktraces

open JuliaLean JuliaLean.base.stacktraces JuliaLean.Registry

variable {MI CI Meth CInfo DI : Type}

/-- Stack-frame equality is precisely equality of the documented source position and flags. -/
def EqualityContract : Prop :=
  ∀ (MI CI Meth CInfo DI : Type) (a b : Frame MI CI Meth CInfo DI),
    eq_StackFrame a b = true ↔
      a.line = b.line ∧ a.from_c = b.from_c ∧ a.func = b.func ∧
      a.file = b.file ∧ a.inlined = b.inlined

theorem equalityContract_proven : EqualityContract := by
  intro MI CI Meth CInfo DI a b
  simp only [eq_StackFrame, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- Equal frames have equal hashes, regardless of code objects and instruction pointers. -/
def HashContract : Prop :=
  ∀ (m : Type → Type) (Io MI CI Meth CInfo DI Mod Ty : Type)
    (c : Callees m Io MI CI Meth CInfo DI Mod Ty)
    (a b : Frame MI CI Meth CInfo DI) (seed : JInt .u64),
    eq_StackFrame a b = true → hash_StackFrame c a seed = hash_StackFrame c b seed

theorem hashContract_proven : HashContract := by
  intro m Io MI CI Meth CInfo DI Mod Ty c a b seed eq
  obtain ⟨line, fromC, func, file, inlined⟩ := (equalityContract_proven _ _ _ _ _ a b).mp eq
  simp only [hash_StackFrame, line, fromC, func, file, inlined]

/-- The shorter constructor does not mark a frame as having recovered debug information. -/
def ConstructorContract : Prop :=
  ∀ (MI CI Meth CInfo DI : Type) (func file : Sym) (line : JInt64)
    (linfo : Linfo MI CI Meth CInfo) (fromC inlined : Bool) (pointer : JInt .u64),
    let frame : Frame MI CI Meth CInfo DI := StackFrame_7 func file line linfo fromC inlined pointer
    frame.pc.val = 0 ∧ frame.debuginfo = none ∧ frame.pointer = pointer

theorem constructorContract_proven : ConstructorContract := by
  intro MI CI Meth CInfo DI func file line linfo fromC inlined pointer
  exact ⟨rfl, rfl, rfl⟩

/-- Module removal removes every matching frame and preserves all other frames in order. -/
def ModuleRemovalContract : Prop :=
  ∀ (m : Type → Type) (MI CI Meth CInfo DI Mod Ty RF : Type)
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (stack : List (Frame MI CI Meth CInfo DI)) (mod : Mod),
    (∀ f ∈ remove_frames_Module r stack mod, from_frame r f mod = false) ∧
    (remove_frames_Module r stack mod).Sublist stack

theorem moduleRemovalContract_proven : ModuleRemovalContract := by
  intro m MI CI Meth CInfo DI Mod Ty RF r stack mod
  constructor
  · intro f hf
    have h := (List.mem_filter.mp hf).2
    simpa using h
  · exact List.filter_sublist

/-- CodeInfo execution contexts are top-level frames for all their source positions. -/
def TopLevelContract : Prop :=
  ∀ (MI CI Meth CInfo DI : Type) (f : Frame MI CI Meth CInfo DI) (info : CInfo),
    f.linfo = .codeInfo info → is_top_level_frame f = true

theorem topLevelContract_proven : TopLevelContract := by
  intro MI CI Meth CInfo DI f info h
  simp [is_top_level_frame, h]

/-- A frame without code information has no discoverable parent module. -/
def MissingModuleContract : Prop :=
  ∀ (m : Type → Type) (MI CI Meth CInfo DI Mod Ty RF : Type)
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (f : Frame MI CI Meth CInfo DI),
    f.linfo = .nothing → parentmodule_StackFrame r f = none

theorem missingModuleContract_proven : MissingModuleContract := by
  intro m MI CI Meth CInfo DI Mod Ty RF r f h
  simp [parentmodule_StackFrame, h]

/-- Removing a named frame never inserts or reorders stack frames. -/
def NameRemovalContract : Prop :=
  ∀ (MI CI Meth CInfo DI : Type) (stack : List (Frame MI CI Meth CInfo DI))
    (name : Sym) (names : List Sym),
    (remove_frames_Symbol stack name).Sublist stack ∧
      (remove_frames_Vector stack names).Sublist stack

theorem nameRemovalContract_proven : NameRemovalContract := by
  intro MI CI Meth CInfo DI stack name names
  exact ⟨List.drop_sublist _ _, List.drop_sublist _ _⟩



abbrev JuliaFrames (MI CI Meth CInfo DI : Type) :=
  { frames : List (Frame MI CI Meth CInfo DI) // ∀ f ∈ frames, f.from_c = false }

private def juliaFramesAppend {MI CI Meth CInfo DI : Type}
    (stack : JuliaFrames MI CI Meth CInfo DI) (frames : List (Frame MI CI Meth CInfo DI)) :
    JuliaFrames MI CI Meth CInfo DI :=
  ⟨stack.val ++ frames.filter (fun frame => !frame.from_c), by
    intro f hf
    rcases List.mem_append.mp hf with hs | hf
    · exact stack.property f hs
    · simpa using (List.mem_filter.mp hf).2⟩

private def checkedTraceLoop {m : Type → Type} [Monad m] [MonadExceptOf StError m]
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    {MI CI Meth CInfo DI Mod Ty RF Io : Type}
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (c : Callees m Io MI CI Meth CInfo DI Mod Ty)
    (stack : JuliaFrames MI CI Meth CInfo DI)
    (cache : List (IP MI CI CInfo × List (Frame MI CI Meth CInfo DI))) :
    List (IP MI CI CInfo) → m (JuliaFrames MI CI Meth CInfo DI)
  | [] => pure stack
  | ip :: ips => do
    let (frames, cache) ← match lookupsGet c cache ip with
      | some frames => pure (frames, cache)
      | none => do
        let frames ← lookup r ip
        pure (frames, cache ++ [(ip, frames)])
    checkedTraceLoop r c (juliaFramesAppend stack frames) cache ips

private theorem checkedTraceLoop_erases {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadExceptOf StError m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    {MI CI Meth CInfo DI Mod Ty RF Io : Type}
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (c : Callees m Io MI CI Meth CInfo DI Mod Ty)
    (trace : List (IP MI CI CInfo)) :
    ∀ stack cache,
      Subtype.val <$> checkedTraceLoop r c stack cache trace =
        stacktrace_loop r c false stack.val cache trace := by
  induction trace with
  | nil => intro stack cache; simp [checkedTraceLoop, stacktrace_loop]
  | cons ip trace ih =>
    intro stack cache
    simp only [checkedTraceLoop, stacktrace_loop, Bool.false_or]
    cases lookupsGet c cache ip <;> simp [map_bind, ih, juliaFramesAppend]

/-- The entire stacktrace result has a certificate that every frame is from Julia.
The equality retains arbitrary runtime effects, exceptions, and divergence in the monad. -/
def NoCFramesContract : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m] [MonadExceptOf StError m]
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (MI CI Meth CInfo DI Mod Ty RF Io : Type)
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (c : Callees m Io MI CI Meth CInfo DI Mod Ty)
    (trace : List (IP MI CI CInfo)),
    ∃ certified : m (JuliaFrames MI CI Meth CInfo DI),
      Subtype.val <$> certified = stacktrace_trace r c trace false

theorem noCFramesContract_proven : NoCFramesContract := by
  intro m instMonad instLawful instExcept instCCPO instMono MI CI Meth CInfo DI Mod Ty RF Io r c trace
  exact ⟨checkedTraceLoop r c ⟨[], by simp⟩ [] trace, checkedTraceLoop_erases r c trace _ _⟩


/-- For C frames the stored statement-index field is the source column. -/
def CLocationContract : Prop :=
  ∀ (m : Type → Type) [Monad m] [MonadExceptOf StError m]
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (MI CI Meth CInfo DI Mod Ty RF : Type)
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (frame : Frame MI CI Meth CInfo DI),
    frame.from_c = true → frame_location r frame =
      pure (SourceLocation.mk (i64 0) (i64 0) frame.pc (i64 0) frame.line (i64 0))

theorem cLocationContract_proven : CLocationContract := by
  intro m instMonad instExcept instCCPO instMono MI CI Meth CInfo DI Mod Ty RF r frame cFrame
  simp [frame_location, cFrame]

/-- The three-argument constructor creates an ordinary, non-inlined Julia frame. -/
def ShortConstructorContract : Prop :=
  ∀ (MI CI Meth CInfo DI : Type) (func file : Sym) (line : JInt64),
    StackFrame_3 (m := Except StError) (MI := MI) (CI := CI) (Meth := Meth)
      (CInfo := CInfo) (DI := DI) (fun x => pure x) (fun x => pure x)
      (fun x => pure x) func file line =
        .ok (StackFrame_9 func file line .nothing false false (JInt.lit .u64 0) (i64 0) none)

theorem shortConstructorContract_proven : ShortConstructorContract := by
  intro MI CI Meth CInfo DI func file line
  rfl


def entries : List Entry := [
  { id := "stacktraces-c-location", juliaFile := "base/stacktraces.jl"
    juliaFns := ["frame_location", "show", "show_spec_linfo", "show_spec_sig", "show_custom_spec_sig"]
    statement := "For C frames the stored statement-index field supplies the source column and the stored line supplies the source line."
    source := "base/stacktraces.jl:312-331", status := .proven
    prop := ``CLocationContract, thm := some ``cLocationContract_proven },
  { id := "stacktraces-short-constructor", juliaFile := "base/stacktraces.jl"
    juliaFns := ["StackFrame(func, file, line)"]
    statement := "The three-argument StackFrame constructor creates an ordinary non-inlined Julia frame with no recovered code information."
    source := "base/stacktraces.jl:84-85", status := .proven
    prop := ``ShortConstructorContract, thm := some ``shortConstructorContract_proven },
  { id := "stacktraces-exclude-c-frames", juliaFile := "base/stacktraces.jl"
    juliaFns := ["stacktrace", "lookup", "_add_linetable_frames!", "_add_di_frames!"]
    statement := "Every frame returned by stacktrace with c_funcs=false comes from Julia rather than C."
    source := "base/stacktraces.jl:233-254", status := .proven
    prop := ``NoCFramesContract, thm := some ``noCFramesContract_proven },
  { id := "stacktraces-equality", juliaFile := "base/stacktraces.jl"
    juliaFns := ["==(::StackFrame, ::StackFrame)"]
    statement := "Stack frames compare equal exactly when their function, file, line, C-origin flag, and inlining flag agree."
    source := "base/stacktraces.jl:99-105", status := .proven
    prop := ``EqualityContract, thm := some ``equalityContract_proven },
  { id := "stacktraces-hash-equality", juliaFile := "base/stacktraces.jl"
    juliaFns := ["hash(::StackFrame, ::UInt)"]
    statement := "Equal stack frames have equal hashes for every seed."
    source := "base/stacktraces.jl:103-115", status := .proven
    prop := ``HashContract, thm := some ``hashContract_proven },
  { id := "stacktraces-constructor-defaults", juliaFile := "base/stacktraces.jl"
    juliaFns := ["StackFrame", "lookup"]
    statement := "The seven-argument constructor preserves the instruction pointer and sets the statement index to zero with no recovered debug information."
    source := "base/stacktraces.jl:82-85", status := .proven
    prop := ``ConstructorContract, thm := some ``constructorContract_proven },
  { id := "stacktraces-remove-module", juliaFile := "base/stacktraces.jl"
    juliaFns := ["remove_frames!(::StackTrace, ::Module)", "from"]
    statement := "Removing a module eliminates every matching frame and leaves the remaining frames in their original order."
    source := "base/stacktraces.jl:283-291,456-458", status := .proven
    prop := ``ModuleRemovalContract, thm := some ``moduleRemovalContract_proven },
  { id := "stacktraces-top-level", juliaFile := "base/stacktraces.jl"
    juliaFns := ["is_top_level_frame", "frame_mi", "frame_method_or_module"]
    statement := "Every CodeInfo execution context is identified as a top-level frame."
    source := "base/stacktraces.jl:293", status := .proven
    prop := ``TopLevelContract, thm := some ``topLevelContract_proven },
  { id := "stacktraces-missing-module", juliaFile := "base/stacktraces.jl"
    juliaFns := ["parentmodule(::StackFrame)", "show", "show_spec_linfo", "show_spec_sig", "show_custom_spec_sig", "frame_location"]
    statement := "Frames without code information have no discoverable parent module."
    source := "base/stacktraces.jl:425-449", status := .proven
    prop := ``MissingModuleContract, thm := some ``missingModuleContract_proven },
  { id := "stacktraces-remove-name-order", juliaFile := "base/stacktraces.jl"
    juliaFns := ["remove_frames!(::StackTrace, ::Symbol)", "remove_frames!(::StackTrace, ::Vector{Symbol})", "stacktrace"]
    statement := "Removing named stack frames never inserts or reorders frames."
    source := "base/stacktraces.jl:273-281", status := .proven
    prop := ``NameRemovalContract, thm := some ``nameRemovalContract_proven }
]

end JuliaLean.Proofs.base.stacktraces
