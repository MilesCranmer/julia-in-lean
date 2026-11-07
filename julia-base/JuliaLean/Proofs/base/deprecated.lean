import JuliaLean.base.strings.substring
import JuliaLean.base.deprecated
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.deprecated

open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.strings.basic (StringData stringDataOps)
open JuliaLean.base.strings.substring (SubString)

private def i (value : Int) : JInt64 := JInt.wrap .i64 value

private def rawStringOps : JuliaLean.base.strings.substring.SubStringOps StringData UInt32 Unit Error where
  ncodeunits := stringDataOps.ncodeunits
  codeunitType := fun _ => ()
  length := fun s first last =>
    (JuliaLean.base.strings.basic.lengthInt stringDataOps s first last).mapError Error.jl
  checkboundsRange := fun s first last =>
    if last.val < first.val ∨ (1 ≤ first.val ∧ last.val ≤ (stringDataOps.ncodeunits s).val) then
      .ok () else .error (.jl .boundsError)
  checkboundsViewRange := fun s first last =>
    if last.val < first.val ∨ (1 ≤ first.val ∧ last.val ≤ s.ncodeunits.val) then
      .ok () else .error (.jl .boundsError)
  isvalid := fun s index => (stringDataOps.isvalid s index).mapError Error.jl
  stringIndexError := fun _ _ => .foreignError "StringIndexError" "invalid string index"
  boundsError := fun _ _ _ => .jl .boundsError
  viewBoundsError := fun _ _ _ => .jl .boundsError
  nextind := fun s index => (stringDataOps.nextind s index (i 1)).mapError Error.jl
  firstindex := JuliaLean.base.strings.basic.firstindexString
  thisindParent := fun s index => (stringDataOps.thisind s index).mapError Error.jl
  isasciiCodeunits := fun units => .ok
    (((units.s.string.bytes.drop units.s.offset.val.toNat).take units.s.ncodeunits.val.toNat).all
      (fun byte => decide (byte.toNat < 128)))
  sizeof := stringDataOps.ncodeunits

private def substringOps (World : Type) :
    JuliaLean.base.deprecated.SubStringOps World StringData (SubString StringData) where
  prevind := fun s index => JuliaLean.base.io.liftJl (stringDataOps.prevind s index (i 1))
  isvalid := fun s index => JuliaLean.base.io.liftJl (stringDataOps.isvalid s index)
  string_index_err := fun _ _ => throw (.foreignError "StringIndexError" "invalid string index")
  raw_substring := fun s first count =>
    match JuliaLean.base.strings.substring.rawSubstring rawStringOps s first count false with
    | .ok view => pure view
    | .error error => throw error

def DeprecatedSubstringValid : Prop :=
  ∀ (World Ip Frame Mod : Type) (ops : JuliaLean.base.deprecated.DepOps World Ip Frame Mod)
    (s : StringData) (first count : JInt64) (before after : World) (view : SubString StringData),
    JuliaLean.base.deprecated.SubString_noshift ops (substringOps World) true s first count before =
      some (.ok (view, after)) →
    0 ≤ view.ncodeunits.val ∧ 0 ≤ view.offset.val ∧
      view.offset.val + view.ncodeunits.val ≤ s.bytes.length

private def silentRuntime : JuliaLean.base.deprecated.DepOps Unit Unit Unit Unit where
  optDepwarn := pure (JInt.wrap .i8 0)
  backtrace := pure []
  lookup := fun _ => pure []
  unknown := ()
  frameEq := fun _ _ => pure true
  fromC := fun _ => false
  func := fun _ => ""
  linfo := fun _ => .other
  file := fun _ => ""
  line := fun _ => i 0
  cNull := ()
  core := ()
  logmsg := fun _ _ _ => pure ()
  isInPureContext := pure false

private def abc : StringData := JuliaLean.base.strings.basic.stringDataOfLeanString "abc"

private theorem negative_count_result :
    JuliaLean.base.deprecated.SubString_noshift silentRuntime (substringOps Unit) true
      abc (i 2) (i (-1)) () = some (.ok (⟨abc, i 2, i (-1)⟩, ())) := by
  rfl

theorem deprecatedSubstringValid_refuted : ¬ DeprecatedSubstringValid := by
  intro h
  have bad := h Unit Unit Unit Unit silentRuntime abc (i 2) (i (-1)) () ()
    ⟨abc, i 2, i (-1)⟩ negative_count_result
  have hn : ¬ 0 ≤ (i (-1)).val := by decide
  exact hn bad.1

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-deprecated-substring-negative-count", juliaFile := "base/deprecated.jl"
    juliaFns := ["SubString{T}(s, i, j, Val(:noshift))"]
    statement := "Every successful deprecated no-shift constructor call returns a SubString with a nonnegative code-unit count and a span inside its parent."
    source := "base/deprecated.jl:704-724; SubString representation invariant"
    status := .refuted, prop := ``DeprecatedSubstringValid
    thm := some ``deprecatedSubstringValid_refuted
    issue := "none found (queries: SubString negative ncodeunits, Val noshift negative SubString, raw_substring negative)"
    notes := "With s=\"abc\", i=2, and j=-1, the installed constructor validates both computed endpoints, then invokes the real raw substring constructor under @inbounds and stores ncodeunits=-1." }
]

end JuliaLean.Proofs.base.deprecated
