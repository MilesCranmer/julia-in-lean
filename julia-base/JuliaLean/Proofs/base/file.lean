import JuliaLean.base.file
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.file

open JuliaLean.Registry

namespace Round1

open JuliaLean JuliaLean.base.file

/-- Reading a public stored DiskStat field returns that field, independently of whether the derived
byte totals fit in Int64.
Julia source: base/file.jl:1664-1690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/runtime_internals.jl:1665-1675;
doc/src/manual/interfaces.md:769-782,818-827;
base/docs/basedocs.jl:3872-3904 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027

The sole premise restores the source's `NTuple{4,UInt64}` field invariant;
all seven scalar fields advertised by `propertynames` range over every UInt64 value. The expected values
are the pre-existing stored fields, not a supplied callback or an assumed
law about `diskStatProperty`. The property is deliberately independent of
the eager byte-total conversions in that function. A constructible
counterexample has bsize = 1 and blocks = typemax(UInt64).
-/
def DiskStatStoredFieldsCorrect : Prop :=
  ∀ (s : DiskStat), s.fspare.length = 4 →
    diskStatProperty (World := Unit) s .ftype () =
      some (.ok (.unsigned s.ftype, ())) ∧
    diskStatProperty (World := Unit) s .bsize () =
      some (.ok (.unsigned s.bsize, ())) ∧
    diskStatProperty (World := Unit) s .blocks () =
      some (.ok (.unsigned s.blocks, ())) ∧
    diskStatProperty (World := Unit) s .bfree () =
      some (.ok (.unsigned s.bfree, ())) ∧
    diskStatProperty (World := Unit) s .bavail () =
      some (.ok (.unsigned s.bavail, ())) ∧
    diskStatProperty (World := Unit) s .files () =
      some (.ok (.unsigned s.files, ())) ∧
    diskStatProperty (World := Unit) s .ffree () =
      some (.ok (.unsigned s.ffree, ()))

/-- A byte observation terminates and is exact when the indicated arithmetic is representable;
outside that case it may exhibit ordinary integer overflow or an InexactError. This is a
specification of an already-observed result, not an operation supplied to the model. -/
def ByteObservationCorrect (exactRequired : Prop) (exactValue : Int)
    (result : Option (Except (JuliaLean.base.io.Error × Unit) (DiskStatValue × Unit))) : Prop :=
  match result with
  | some (.ok (.signed value, ())) => exactRequired → value.val = exactValue
  | some (.error (.jl (.inexactError _), ())) => ¬exactRequired
  | _ => False

/-- DiskStat's total and available readings are exact when their counts are representable,
used is exact when both counts are representable, and successful readings conserve bytes.
Julia source: base/file.jl:1669-1700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/file.jl:1664-1668,1695-1700;
base/runtime_internals.jl:1665-1675;
doc/src/manual/integers-and-floating-point-numbers.md:231-249
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027

This is an accounting/coherence invariant, not an unconditional no-overflow
claim. Every constructible input is included. Each observation is checked
separately and must terminate. An unrepresentable total does not license
failure of a representable available count. For used, exactness requires
both input byte counts to fit, avoiding a promise of cancellation through
overflow. No coupling of failure
payloads, no successful-run hypothesis, and no arithmetic-range hypothesis
is imposed. The specification does not copy the model's modular products
or its eager, ordered conversion tests.
-/
def DiskStatByteAccountingCorrect : Prop :=
  ∀ (s : DiskStat), s.fspare.length = 4 →
    let exactTotal := s.bsize.val * s.blocks.val
    let exactAvailable := s.bsize.val * s.bavail.val
    let totalFits := 0 ≤ exactTotal ∧ exactTotal < (2 : Int) ^ 63
    let availableFits := 0 ≤ exactAvailable ∧ exactAvailable < (2 : Int) ^ 63
    let totalResult := diskStatProperty (World := Unit) s .total ()
    let availableResult := diskStatProperty (World := Unit) s .available ()
    let usedResult := diskStatProperty (World := Unit) s .used ()
    ByteObservationCorrect totalFits exactTotal totalResult ∧
    ByteObservationCorrect availableFits exactAvailable availableResult ∧
    ByteObservationCorrect (totalFits ∧ availableFits) (exactTotal - exactAvailable) usedResult ∧
    match totalResult, availableResult, usedResult with
    | some (.ok (.signed total, ())), some (.ok (.signed available, ())),
        some (.ok (.signed used, ())) =>
        total.val = used.val + available.val
    | _, _, _ => True

end Round1

end JuliaLean.Proofs.base.file

namespace JuliaLean.ChatGPT.Batch4.Group23
open JuliaLean JuliaLean.base.file JuliaLean.Proofs.base.file.Round1

def diskStatCounterexample : DiskStat where
  ftype := JInt.wrap .u64 0
  bsize := JInt.wrap .u64 1
  blocks := JInt.wrap .u64 18446744073709551615
  bfree := JInt.wrap .u64 0
  bavail := JInt.wrap .u64 0
  files := JInt.wrap .u64 0
  ffree := JInt.wrap .u64 0
  fspare := List.replicate 4 (JInt.wrap .u64 0)

theorem FilesDiskstatStoredFields_refuted :
    ¬ JuliaLean.Proofs.base.file.Round1.DiskStatStoredFieldsCorrect := by
  intro h
  have bad := (h diskStatCounterexample (by decide)).2.1
  cases bad

theorem FilesDiskstatByteAccounting_refuted :
    ¬ JuliaLean.Proofs.base.file.Round1.DiskStatByteAccountingCorrect := by
  intro h
  have bad := (h diskStatCounterexample (by decide)).2.1
  exact bad (by decide)

end JuliaLean.ChatGPT.Batch4.Group23

namespace JuliaLean.Proofs.base.file
open JuliaLean.Registry

namespace LegacyMethods

open JuliaLean JuliaLean.base.file

section InternalHelpers

variable {World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
  WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal : Type}
  (ops : FileOps World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent
    Stream WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal)

-- Source reference: base/file.jl:359-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
theorem isWithin_route (inner outer : String) :
    isWithin ops inner outer = (if inner == outer then pure true else do
      let boundary ← ops.joinpath [outer, ""]
      pure (inner.startsWith boundary)) := rfl

-- Source reference: base/file.jl:260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
theorem delayedDeleteRef_route :
    delayedDeleteRef ops = (do
      let parent ← tempdirFn ops
      ops.joinpath [parent, "julia_delayed_deletes_ref"]) := rfl

end InternalHelpers

abbrev MoveAction (World Error Result : Type) :=
  World → Option (Except (Error × World) (Result × World))

def MvMethods : Prop :=
  ∀ (World Error Source Destination : Type)
    (replace noreplace : Source → Destination → MoveAction World Error Destination)
    (src : Source) (dst : Destination) (force : Bool) (world : World),
    mvWith replace noreplace src dst force world =
      if force then replace src dst world else noreplace src dst world

theorem mvMethods : MvMethods := by
  intro World Error Source Destination replace noreplace src dst force world
  cases force <;> rfl

theorem mvNoreplace_route
    {World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
      WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal : Type}
    (ops : FileOps World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent
      Stream WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal) (src dst : String) :
    mvNoreplace ops src dst = (do
      checkforMvCpCptree ops src dst "moving" false false
      tryCatchM (do let _ ← rename ops src dst; pure ()) (fun error => do
        if !isIOError ops error then throw error
        if isIOErrorCode ops error ops.uvEnoent then throw error
        let _ ← cp ops src dst false false
        rm ops src false true true)
      pure dst) := rfl

/-- Permissions are accepted exactly in the POSIX permission-bit range. -/
def CheckmodeMethod : Prop :=
  ∀ (World N : Type) (intOps : IntegerOps World N) (mode : N) (world : World),
    checkmode mode intOps world =
      if 0 ≤ intOps.value mode ∧ intOps.value mode ≤ 511 then
        some (.ok (mode, world))
      else some (.error (.jl (.argumentError "Mode must be between 0 and 511 = 0o777"), world))

theorem checkmodeMethod : CheckmodeMethod := by
  intro World N intOps mode world
  by_cases h : 0 ≤ intOps.value mode ∧ intOps.value mode ≤ 511
  · simp only [checkmode, h]
    rfl
  · simp only [checkmode, h]
    rfl

end LegacyMethods

def entries : List Entry := [
  { id := "files-method-mv", juliaFile := "base/file.jl"
    juliaFns := ["mv"]
    statement := "mv dispatches exactly to replacement or no-replacement behavior from the force keyword."
    source := "base/file.jl:505-511", status := .proven
    prop := ``LegacyMethods.MvMethods, thm := some ``LegacyMethods.mvMethods },
  { id := "files-method-checkmode", juliaFile := "base/file.jl"
    juliaFns := ["checkmode"]
    statement := "checkmode returns every integer in 0:0o777 and raises ArgumentError for every integer outside that interval."
    source := "base/file.jl:151-157", status := .proven
    prop := ``LegacyMethods.CheckmodeMethod, thm := some ``LegacyMethods.checkmodeMethod },
  { id := "files-diskstat-stored-fields", juliaFile := "base/file.jl",
    juliaFns := ["getproperty(::DiskStat, ::Symbol)", "propertynames(::DiskStat)", "diskstat"],
    statement := "Reading any advertised stored DiskStat property (ftype, bsize, blocks, bfree, bavail, files, ffree) returns the stored field, independently of whether the derived byte totals fit in Int64.",
    source := "base/file.jl:1664-1695 (DiskStat, getproperty, propertynames)", status := .refuted,
    prop := ``JuliaLean.Proofs.base.file.Round1.DiskStatStoredFieldsCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group23.FilesDiskstatStoredFields_refuted,
    issue := "none found; related PR #42959 (queries: issues: DiskStat InexactError; issues: diskstat overflow; prs: DiskStat; issues: DiskStat)",
    notes := "Expected refutation: getproperty converts bsize*blocks to Int64 first, so bsize=1, blocks=typemax(UInt64) makes s.bsize throw InexactError." },
  { id := "files-diskstat-byte-accounting", juliaFile := "base/file.jl",
    juliaFns := ["getproperty(::DiskStat, ::Symbol)", "diskstat"],
    statement := "DiskStat total and available are exact when their byte counts are representable, used is exact when both are, and successful readings satisfy total = used + available; an unrepresentable total does not make a representable available count fail.",
    source := "base/file.jl:1664-1700 (DiskStat, getproperty, diskstat)", status := .refuted,
    prop := ``JuliaLean.Proofs.base.file.Round1.DiskStatByteAccountingCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group23.FilesDiskstatByteAccounting_refuted,
    issue := "none found; related PR #42959 (queries: issues: DiskStat InexactError; issues: diskstat overflow; prs: DiskStat; issues: DiskStat)",
    notes := "Expected refutation: bsize=1, blocks=typemax(UInt64), bavail=0 makes available throw InexactError because the total is converted first." }
]

end JuliaLean.Proofs.base.file
