import JuliaLean.base.loading
import JuliaLean.base.tuple
import JuliaLean.base.operators
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.tuple


namespace JuliaLean.Proofs.base.loading.ValueContracts

open JuliaLean JuliaLean.base.loading JuliaLean.Registry

def MissingDependencyStanza : Prop :=
  ∀ name : Bytes, dep_stanza_get_Nothing name = none

def MissingPackageLiteral : Prop :=
  ∀ value : Unit, pkg_str_nothing value = lit "nothing"

def StringTriggerExact : Prop :=
  ∀ trigger name : Bytes, ext_may_load_weakdep (.str trigger) name = true ↔ trigger = name

def FileMacroSourceInformation : Prop :=
  macro_FILE none = none ∧ ∀ file : Bytes, macro_FILE (some file) = some file

/-- Counters use native wrapping Int64 arithmetic, including typemax overflow. -/
def RejectionCounterIncrement : Prop :=
  ∀ (before : AMap Bytes JInt64) (reason : Bytes),
    let (after, returned) := record_reason before reason
    returned.val = (JInt.wrap .i64 (((before.get reason).getD (i64 0)).val + 1)).val ∧
    after.get reason = some returned ∧
    ∀ other : Bytes, other ≠ reason → after.get other = before.get other

/-- Compile-time preference tracking is a set insertion: observations remain recorded,
other packages' observations are untouched, and repeated recording has no further effect. -/
def PreferenceRecordingSetSemantics : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V)
    (uuid : JuliaLean.base.uuid.UUID) (key : Bytes) (before : World X D CI CF),
    ∃ after : World X D CI CF,
      StateT.run (ExceptT.run (record_compiletime_preference o uuid key)) before = some (.ok (), after) ∧
      key ∈ (after.compiletime_preferences.get uuid).getD [] ∧
      (∀ other : JuliaLean.base.uuid.UUID, other ≠ uuid →
        after.compiletime_preferences.get other = before.compiletime_preferences.get other) ∧
      StateT.run (ExceptT.run (record_compiletime_preference o uuid key)) after = some (.ok (), after)

theorem missingDependencyStanza_proven : MissingDependencyStanza := by
  intro name
  rfl

theorem missingPackageLiteral_proven : MissingPackageLiteral := by
  intro value
  rfl

theorem stringTriggerExact_proven : StringTriggerExact := by
  intro trigger name
  simp [ext_may_load_weakdep, ext_may_load_weakdep_string]

theorem fileMacroSourceInformation_proven : FileMacroSourceInformation := by
  exact ⟨rfl, fun _ => rfl⟩


def entries : List Entry := [
  { id := "loading-missing-dependency-stanza", juliaFile := "base/loading.jl"
    juliaFns := ["dep_stanza_get(::Nothing, ::String)"]
    statement := "An absent dependency stanza never resolves a package name."
    source := "base/loading.jl:1147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``MissingDependencyStanza, thm := some ``missingDependencyStanza_proven },
  { id := "loading-missing-package-literal", juliaFile := "base/loading.jl"
    juliaFns := ["_pkg_str(::Nothing)"]
    statement := "Serializing an absent package produces the Julia literal nothing."
    source := "base/loading.jl:3682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``MissingPackageLiteral, thm := some ``missingPackageLiteral_proven },
  { id := "loading-string-trigger-exact", juliaFile := "base/loading.jl"
    juliaFns := ["ext_may_load_weakdep(::String, ::String)"]
    statement := "A single String extension trigger authorizes exactly the package with that name."
    source := "base/loading.jl:782 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``StringTriggerExact, thm := some ``stringTriggerExact_proven },
  { id := "loading-file-macro-source-information", juliaFile := "base/loading.jl"
    juliaFns := ["@__FILE__"]
    statement := "The file macro retains the parser's filename, including an empty filename, and returns nothing when source information is absent."
    source := "base/loading.jl:5149-5152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``FileMacroSourceInformation, thm := some ``fileMacroSourceInformation_proven },
  { id := "loading-rejection-counter-increment", juliaFile := "base/loading.jl"
    juliaFns := ["record_reason(::Dict{Symbol,Int}, ::Symbol)"]
    statement := "Recording a reason increments and returns its native wrapping Int64 count, starting at one, while preserving other counters."
    source := "base/loading.jl:4692-4694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .todo, prop := ``RejectionCounterIncrement },
  { id := "loading-preference-recording-set-semantics", juliaFile := "base/loading.jl"
    juliaFns := ["record_compiletime_preference(::UUID, ::String)"]
    statement := "Recording a compile-time preference inserts the key, preserves other packages' observations, and is idempotent."
    source := "base/loading.jl:4604-4608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .todo, prop := ``PreferenceRecordingSetSemantics }
]

end JuliaLean.Proofs.base.loading.ValueContracts

namespace JuliaLean.Proofs.base.loading.Round1

open JuliaLean JuliaLean.base.loading

/-- Mathematical value of a digest, with the first byte most significant.
This specification does not call a comparison function or encode an expected
result in a callback. -/
def ShaMagnitude (bytes : List UInt8) : Nat :=
  bytes.foldl (fun value byte => 256 * value + byte.toNat) 0

/-- Representation adapter from a Lean byte to Julia's modeled UInt8. -/
def ShaByte (byte : UInt8) : JInt .u8 :=
  JInt.wrap .u8 (Int.ofNat byte.toNat)

/-- Bind the two operations actually reached by `tuple.islessTuple` to the
installed integer and operator models. The other tuple operation fields are
not read by `islessShort`, `islessLong`, or `islessTuple` (tuple.lean:1927-1952,
2129-2131), and remain universally quantified rather than assumed correct. -/
def ShaOrderBindings {X Y E D CI CF V : Type}
    (o : LOps X Y E D CI CF V) (tupleOps : JuliaLean.base.tuple.Ops UInt8) :
    LOps X Y E D CI CF V :=
  { o with
    isless_bytes := JuliaLean.base.tuple.islessTuple
      { tupleOps with
        isequal := JuliaLean.base.operators.isequalDefault
          (fun a b => JuliaLean.base.int.eqSame (ShaByte a) (ShaByte b))
        isless := JuliaLean.base.operators.islessReal
          (fun a b => JuliaLean.base.int.lt_BitUnsigned (ShaByte a) (ShaByte b)) } }

/-- SHA1 and SHA256 equality compares the complete represented digest value.
Julia source: base/loading.jl:114-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:109-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
The length hypotheses are the NTuple{20,UInt8}/NTuple{32,UInt8} field invariants;
they exclude values the model's unconstrained List field admits but Julia cannot.
-/
def ShaEqualityCorrect : Prop :=
  ∀ (n : Nat) (a b : SHA n),
    (n = 20 ∨ n = 32) → a.bytes.length = n → b.bytes.length = n →
    (eq_SHA a b = true ↔ ShaMagnitude a.bytes = ShaMagnitude b.bytes)

/-- SHA1 and SHA256 ordering agrees with the strict order of their complete
big-endian digest values, hence is a strict total order on each digest type.
Julia source: base/loading.jl:114-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:205-225; base/tuple.jl:648-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Both actual digest widths are included, so the short-tuple and Any32-tuple paths
are both in scope; no arithmetic on unbounded Julia lengths occurs here.
-/
def ShaOrderingCorrect : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V)
      (tupleOps : JuliaLean.base.tuple.Ops UInt8) (n : Nat) (a b : SHA n),
    (n = 20 ∨ n = 32) → a.bytes.length = n → b.bytes.length = n →
    (isless_SHA (ShaOrderBindings o tupleOps) a b = true ↔
      ShaMagnitude a.bytes < ShaMagnitude b.bytes)

end JuliaLean.Proofs.base.loading.Round1

section

namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.loading
open _root_.JuliaLean.Proofs.base.loading.Round1

def shaMagnitudeModel (bytes : List UInt8) : Nat :=
  bytes.foldl (fun value byte => 256 * value + byte.toNat) 0

def shaByteModel (byte : UInt8) : JInt .u8 :=
  JInt.wrap .u8 (Int.ofNat byte.toNat)

/-- Positional base-256 value, with the head byte most significant. -/
def shaPlaceValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + shaPlaceValue bs

theorem shaFoldlValue (bs : List UInt8) (acc : Nat) :
    bs.foldl (fun value byte => 256 * value + byte.toNat) acc =
      256 ^ bs.length * acc + shaPlaceValue bs := by
  induction bs generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.one_mul,
      shaPlaceValue, Nat.add_zero]
  | cons b bs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, shaPlaceValue, Nat.pow_succ,
      Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

theorem shaMagnitudeValue (bs : List UInt8) : shaMagnitudeModel bs = shaPlaceValue bs := by
  unfold shaMagnitudeModel
  rw [shaFoldlValue]
  exact Nat.zero_add _

theorem shaPlaceBound (bs : List UInt8) : shaPlaceValue bs < 256 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    have hb : b.toNat + 1 ≤ 256 := b.toNat_lt
    have hm := Nat.mul_le_mul_right (256 ^ bs.length) hb
    simp only [Nat.add_mul, Nat.one_mul] at hm
    simp only [shaPlaceValue, List.length_cons, Nat.pow_succ]
    have hprod : 256 * 256 ^ bs.length = 256 ^ bs.length * 256 := Nat.mul_comm _ _
    omega

theorem shaDigitsLt (a b x y k : Nat) (hx : x < k) (hy : y < k) :
    a * k + x < b * k + y ↔ a < b ∨ (a = b ∧ x < y) := by
  by_cases hab : a < b
  · have hm : (a + 1) * k ≤ b * k := Nat.mul_le_mul_right k hab
    simp only [Nat.add_mul, Nat.one_mul] at hm
    constructor
    · intro _; exact Or.inl hab
    · intro _; omega
  · by_cases hba : b < a
    · have hm : (b + 1) * k ≤ a * k := Nat.mul_le_mul_right k hba
      simp only [Nat.add_mul, Nat.one_mul] at hm
      constructor
      · intro h; omega
      · intro h; rcases h with h | ⟨h, _⟩ <;> omega
    · have heq : a = b := by omega
      subst b
      simp only [Nat.lt_irrefl, false_or, true_and, Nat.add_lt_add_iff_left]

theorem shaDigitsEq (a b x y k : Nat) (hx : x < k) (hy : y < k)
    (heq : a * k + x = b * k + y) : a = b ∧ x = y := by
  have hab : ¬ a < b := by
    intro h
    have := (shaDigitsLt a b x y k hx hy).mpr (Or.inl h)
    omega
  have hba : ¬ b < a := by
    intro h
    have := (shaDigitsLt b a y x k hy hx).mpr (Or.inl h)
    omega
  have he : a = b := by omega
  subst b
  exact ⟨rfl, by omega⟩

theorem shaPlaceInjective (a b : List UInt8) (hlen : a.length = b.length)
    (hvalue : shaPlaceValue a = shaPlaceValue b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons x xs => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
    cases b with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons y ys =>
      have ht : xs.length = ys.length := Nat.succ.inj hlen
      have hx := shaPlaceBound xs
      have hy := shaPlaceBound ys
      rw [← ht] at hy
      simp only [shaPlaceValue, ← ht] at hvalue
      obtain ⟨hbyte, htail⟩ := shaDigitsEq _ _ _ _ _ hx hy hvalue
      have hxy : x = y := UInt8.toNat_inj.mp hbyte
      rw [hxy, ih ys ht htail]

theorem shaEqualityBytes (a b : List UInt8) (hlen : a.length = b.length) :
    (a == b) = true ↔ shaMagnitudeModel a = shaMagnitudeModel b := by
  rw [shaMagnitudeValue, shaMagnitudeValue]
  rw [beq_iff_eq]
  constructor
  · intro h; rw [h]
  · exact shaPlaceInjective a b hlen

/-- The primitive byte adapter retains the byte's natural value. -/
theorem shaByteVal (b : UInt8) : (shaByteModel b).val = (b.toNat : Int) := by
  change wrapInt .u8 (b.toNat : Int) = _
  apply wrapInt_of_inRange
  have hb := b.toNat_lt
  change 0 ≤ (b.toNat : Int) ∧ (b.toNat : Int) ≤ 255
  omega

theorem shaByteBits (b : UInt8) : (JuliaLean.C.fromJInt (shaByteModel b)).toNat = b.toNat := by
  unfold JuliaLean.C.fromJInt
  rw [shaByteVal, BitVec.toNat_ofInt]
  change ((b.toNat : Int) % 256).toNat = b.toNat
  have hb := b.toNat_lt
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

def shaTupleBindings (ops : JuliaLean.base.tuple.Ops UInt8) :
    JuliaLean.base.tuple.Ops UInt8 :=
  { ops with
    isequal := fun a b => JuliaLean.base.int.eqSame (shaByteModel a) (shaByteModel b)
    isless := fun a b => JuliaLean.base.int.lt_BitUnsigned (shaByteModel a) (shaByteModel b) }

theorem shaTupleEqual (ops : JuliaLean.base.tuple.Ops UInt8) (a b : UInt8) :
    (shaTupleBindings ops).isequal a b = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  change (JuliaLean.C.fromJInt (shaByteModel a) == JuliaLean.C.fromJInt (shaByteModel b)) = true ↔
    (a == b) = true
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [shaByteBits, shaByteBits] at hn
    exact UInt8.toNat_inj.mp hn
  · intro h; rw [h]

theorem shaTupleLess (ops : JuliaLean.base.tuple.Ops UInt8) (a b : UInt8) :
    (shaTupleBindings ops).isless a b = decide (a.toNat < b.toNat) := by
  change decide ((JuliaLean.C.fromJInt (shaByteModel a)).toNat <
    (JuliaLean.C.fromJInt (shaByteModel b)).toNat) = _
  rw [shaByteBits, shaByteBits]

theorem shaShortCorrect (ops : JuliaLean.base.tuple.Ops UInt8) (a b : List UInt8)
    (hlen : a.length = b.length) :
    JuliaLean.base.tuple.islessShort (shaTupleBindings ops) a b = true ↔
      shaPlaceValue a < shaPlaceValue b := by
  induction a generalizing b with
  | nil =>
    have hb : b = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst b
    simp only [JuliaLean.base.tuple.islessShort, JuliaLean.base.tuple.islessEmptyEmpty,
      Bool.false_eq_true, shaPlaceValue, Nat.lt_irrefl]
  | cons x xs ih =>
    cases b with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons y ys =>
      have ht := Nat.succ.inj hlen
      have hx := shaPlaceBound xs
      have hy := shaPlaceBound ys
      rw [← ht] at hy
      simp only [JuliaLean.base.tuple.islessShort, shaTupleEqual, shaTupleLess,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ih ys ht,
        shaPlaceValue, ← ht, shaDigitsLt _ _ _ _ _ hx hy]
      rw [UInt8.toNat_inj]

/-- Advancing an index through two cons cells commutes with the long tuple loop. -/
theorem shaLongTail (ops : JuliaLean.base.tuple.Ops UInt8) (a b : UInt8)
    (as bs : List UInt8) (i k : Nat) :
    JuliaLean.base.tuple.islessLong ops (a :: as) (b :: bs) (i + 1) k =
      JuliaLean.base.tuple.islessLong ops as bs i k := by
  induction k generalizing i with
  | zero => simp only [JuliaLean.base.tuple.islessLong, List.length_cons,
      Nat.succ_lt_succ_iff]
  | succ k ih =>
    simp only [JuliaLean.base.tuple.islessLong, List.getElem?_cons_succ,
      List.length_cons, Nat.succ_lt_succ_iff]
    cases ha : as[i]? <;> cases hb : bs[i]? <;> simp only [ha, hb]
    split
    · rfl
    · exact ih (i + 1)

theorem shaLongShort (ops : JuliaLean.base.tuple.Ops UInt8) (a b : List UInt8)
    (hlen : a.length = b.length) :
    JuliaLean.base.tuple.islessLong (shaTupleBindings ops) a b 0 a.length =
      JuliaLean.base.tuple.islessShort (shaTupleBindings ops) a b := by
  induction a generalizing b with
  | nil =>
    have hb : b = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst b
    rfl
  | cons x xs ih =>
    cases b with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons y ys =>
      have ht := Nat.succ.inj hlen
      simp only [List.length_cons, JuliaLean.base.tuple.islessLong,
        List.getElem?_cons_zero, shaTupleEqual, shaTupleLess]
      rw [shaLongTail, ih ys ht]
      simp only [JuliaLean.base.tuple.islessShort, shaTupleEqual, shaTupleLess]
      by_cases he : x = y
      · subst y
        simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false,
          Nat.lt_irrefl, decide_false, Bool.false_or, Bool.true_and]
      · have hb : (x == y) = false := beq_eq_false_iff_ne.mpr he
        simp only [hb, Bool.not_false, ite_true, Bool.false_and, Bool.or_false]

theorem shaOrderingModel (tupleOps : JuliaLean.base.tuple.Ops UInt8) (a b : List UInt8)
    (hlen : a.length = b.length) :
    JuliaLean.base.tuple.islessTuple (shaTupleBindings tupleOps) a b = true ↔
      shaMagnitudeModel a < shaMagnitudeModel b := by
  rw [shaMagnitudeValue, shaMagnitudeValue]
  unfold JuliaLean.base.tuple.islessTuple
  split
  · rw [Nat.min_eq_left (Nat.le_of_eq hlen), shaLongShort tupleOps _ _ hlen]
    exact shaShortCorrect tupleOps _ _ hlen
  · exact shaShortCorrect tupleOps _ _ hlen

theorem LoadingMethod143V2_proven : JuliaLean.Proofs.base.loading.Round1.ShaEqualityCorrect := by
  intro n a b hn ha hb
  exact shaEqualityBytes a.bytes b.bytes (ha.trans hb.symm)

theorem LoadingMethod141V2_proven : JuliaLean.Proofs.base.loading.Round1.ShaOrderingCorrect := by
  intro X Y E D CI CF V o tupleOps n a b hn ha hb
  exact shaOrderingModel tupleOps a.bytes b.bytes (ha.trans hb.symm)

end JuliaLean.ChatGPT.Batch4.Group11
end

namespace JuliaLean.Proofs.base.loading

open JuliaLean JuliaLean.base.loading JuliaLean.Registry
open JuliaLean.base.pkgid (PkgId)

/-- `identify_stdlib_project_dep` returns `nothing` when the stdlib directory has no
project file (`stdlib_projfile === nothing && return nothing`, base/loading.jl:440). -/
def StdlibProjectDepMissingProject : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V) (stdlib : PkgId) (depname : Bytes)
    (w w' : World X D CI CF) (b : Bool),
    ((do locate_project_file o (← joinpath o [o.STDLIB, stdlib.name])) : LM o _).run.run w =
      some (.ok (.inl b), w') →
    ∃ w'', (identify_stdlib_project_dep o stdlib depname).run.run w = some (.ok none, w'')

def entries : List Entry := [
  { id := "loading-method-141-v2", juliaFile := "base/loading.jl"
    juliaFns := ["isless(::SHA1, ::SHA1)", "isless(::SHA256, ::SHA256)"]
    statement := "SHA1 and SHA256 ordering agrees with the strict order of their complete big-endian digest values, hence is a strict total order on each digest type."
    source := "base/loading.jl:114-141; base/operators.jl:205-225; base/tuple.jl:648-661 (isless documentation)"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Round1.ShaOrderingCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.LoadingMethod141V2_proven },
  { id := "loading-method-143-v2", juliaFile := "base/loading.jl"
    juliaFns := ["==(::SHA1, ::SHA1)", "==(::SHA256, ::SHA256)"]
    statement := "SHA1 and SHA256 equality returns true exactly when their complete big-endian digest values agree."
    source := "base/loading.jl:114-143; base/operators.jl:109-118 (== documentation)"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Round1.ShaEqualityCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.LoadingMethod143V2_proven
    notes := "HELD for source coverage: the installed eq_SHA (JuliaLean/base/loading.lean:729) compares Lean lists with BEq and bypasses tuple.eqTuple (JuliaLean/base/tuple.lean:2122) and the UInt8 == model, so a proof would not reach Julia's tuple == until that mirror is repaired. The statement is approved and unchanged." },
  { id := "loading-stdlib-project-dep-missing-project", juliaFile := "base/loading.jl"
    juliaFns := ["identify_stdlib_project_dep(stdlib::PkgId, depname::String)"]
    statement := "identify_stdlib_project_dep returns nothing when the stdlib directory has no project file."
    source := "base/loading.jl:433-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.StdlibProjectDepMissingProject
    notes := "locate_project_file returns true, never nothing, when no project file exists, so the `=== nothing` check never fires and explicit_project_deps_get(true, depname) throws MethodError. Reproduced on Julia 1.13.2 and nightly (repro/loading-stdlib-project-dep-missing-project.jl). The model shows the MethodError branch; the Lean refutation needs a concrete LOps instance, which no proof file builds yet." }
]

end JuliaLean.Proofs.base.loading

namespace JuliaLean.Proofs.base.loading.Models1Group9.SHAIO

open JuliaLean
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group9.SHAIO
open JuliaLean.base.show
open JuliaLean.base.strings.io

/-- An observation of one existing IOPrims/CharIO runtime dispatch.
Bytes record the arguments requested, including a dispatch that throws;
they do not claim that a failed stream actually committed every requested byte. -/
inductive Event where
  | lock (stream : Nat)
  | unlock (stream : Nat)
  | bytes (stream : Nat) (value : List UInt8)
  | byte (stream : Nat) (value : UInt8)
  deriving DecidableEq, Repr

def Event.stream : Event → Nat
  | .lock s | .unlock s | .bytes s _ | .byte s _ => s

def Event.requested : Event → List UInt8
  | .bytes _ bs => bs
  | .byte _ b => [b]
  | _ => []

structure Attempt where
  event : Event
  succeeded : Bool
  deriving DecidableEq, Repr

structure ProbeState where
  attempts : List Attempt := []
  /-- Zero-based primitive calls that throw; positions past the end are irrelevant. -/
  failures : List Nat := []

inductive ProbeError where
  | primitive (call : Nat)
  | jl
  | char
  | string (error : JuliaLean.Strings.SErr)
  deriving DecidableEq, Repr

abbrev ProbeM := EStateM ProbeError ProbeState

/-- Observer lifts retain the exceptional outcome as a distinct error tag.
The subjects do not catch either lifted exception class. -/
instance : MonadLiftT (Except JlError) ProbeM where
  monadLift result := match result with
    | .ok value => pure value
    | .error _ => throwThe ProbeError .jl

instance : MonadLiftT (Except JuliaLean.base.char.CharError) ProbeM where
  monadLift result := match result with
    | .ok value => pure value
    | .error _ => throwThe ProbeError .char

/-- Preserve the selected String concatenation exception before any IO dispatch. -/
instance : MonadLiftT (Except JuliaLean.Strings.SErr) ProbeM where
  monadLift result := match result with
    | .ok value => pure value
    | .error error => throwThe ProbeError (.string error)

/-- A concrete error-injecting observer of the pre-existing IO primitive boundary.
It retains every attempted call in state before returning or throwing. No
correctness law about a supplied printer is assumed. -/
def observe (event : Event) : ProbeM Unit := fun state =>
  let fails := state.failures.contains state.attempts.length
  let next := { state with attempts := state.attempts ++ [⟨event, !fails⟩] }
  if fails then .error (.primitive state.attempts.length) next else .ok () next

def probePrims : IOPrims ProbeM Nat Unit where
  write stream bytes := observe (.bytes stream bytes)
  lock stream := observe (.lock stream)
  unlock stream := observe (.unlock stream)
  get _ _ := none
  displaysize _ := pure (JInt.wrap .i64 24, JInt.wrap .i64 80)

def probeCharIO : CharIO ProbeM Nat Unit where
  prims := probePrims
  writeByte stream byte := do
    observe (.byte stream byte)
    pure (JInt.wrap .i64 1)

/-- The stream identity that an IOContext exposes to the installed dispatch. -/
def streamOf : JIO Nat Unit → Nat
  | .plain stream => stream
  | .context context => context.io

def requestedBytes (attempts : List Attempt) : List UInt8 :=
  attempts.flatMap (fun attempt => attempt.event.requested)

/-- Mathematical lowercase hexadecimal digits, independent of the model's
bit shifts, table lookup, tuple iterator and Char representation. -/
def digitValue (byte : UInt8) : Option Nat :=
  if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then some (byte.toNat - 48)
  else if 97 ≤ byte.toNat ∧ byte.toNat ≤ 102 then some (byte.toNat - 87)
  else none

/-- Positional hexadecimal encoding, including the exact output length. -/
def Encodes (input output : List UInt8) : Prop :=
  output.length = 2 * input.length ∧
  ∀ (i : Nat) (byte : UInt8), input[i]? = some byte →
    ∃ high low highValue lowValue,
      output[2 * i]? = some high ∧ output[2 * i + 1]? = some low ∧
      digitValue high = some highValue ∧ digitValue low = some lowValue ∧
      byte.toNat = 16 * highValue + lowValue

/-- Every successful lock has one attempted unlock, even if that unlock is
itself the failing primitive. An unsuccessful lock needs no unlock. -/
def CleanupBalanced (attempts : List Attempt) : Prop :=
  (attempts.filter (fun a => match a.event with
    | .lock _ => a.succeeded | _ => false)).length =
  (attempts.filter (fun a => match a.event with
    | .unlock _ => true | _ => false)).length

/-- Once a primitive throws, only finally-block unlocks may be dispatched. -/
def OnlyCleanupAfterFailure (attempts : List Attempt) : Prop :=
  ∀ (i : Nat) (a : Attempt), attempts[i]? = some a → a.succeeded = false →
    ∀ (j : Nat) (b : Attempt), i < j → attempts[j]? = some b →
      ∃ stream, b.event = .unlock stream

def IsPrefix (initial full : List UInt8) : Prop := ∃ rest, full = initial ++ rest

/-- Independent observable result specification for a complete digest output.
Every runtime call targets the supplied stream. The primitive fault schedule
is arbitrary, and error cases retain the requested byte prefix and cleanup. -/
def Emission (stream : Nat) (Output : List UInt8 → Prop)
    (result : EStateM.Result ProbeError ProbeState Unit) : Prop :=
  let state := match result with | .ok _ state | .error _ state => state
  CleanupBalanced state.attempts ∧ OnlyCleanupAfterFailure state.attempts ∧
  (∀ a ∈ state.attempts, a.event.stream = stream) ∧
  match result with
  | .ok _ _ =>
      Output (requestedBytes state.attempts) ∧
      (∀ a ∈ state.attempts, a.succeeded = true)
  | .error (.primitive call) _ =>
      (∃ failed, state.attempts[call]? = some failed ∧ failed.succeeded = false) ∧
      (∀ j a, call < j → state.attempts[j]? = some a → a.succeeded = true) ∧
      ∃ full, Output full ∧ IsPrefix (requestedBytes state.attempts) full
  | .error _ _ => False

/-- SHA1 and SHA256 print request exactly two lowercase hex digits per byte,
in digest order, with no delimiters. Every possible primitive failure schedule
propagates the primitive error, preserves the requested prefix and performs
all applicable unlock attempts; IOContext forwarding preserves stream identity.
The sole input condition is the source NTuple field invariant.
Julia source: base/loading.jl:114-138; base/strings/util.jl:1286-1291,1329-1334;
base/strings/io.jl:42-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrintCorrect : Prop :=
  ∀ (kind : Kind) (hash : SHA kind.width) (io : JIO Nat Unit) (failures : List Nat),
    hash.bytes.length = kind.width →
    Emission (streamOf io) (Encodes hash.bytes)
      (printDigest probeCharIO io kind hash { failures := failures })

/-- SHA show's constructor syntax surrounds the independent hexadecimal output.
Every raw prefix allocation outcome and fresh byte value is included. Refusal
of its6/8-byte String allocation yields OutOfMemoryError before any IO event;
success retains the complete arbitrary primitive-error/cleanup contract.
The expected prefix spelling and hexadecimal relation do not call the prefix
builder, String copy or output implementation.
Julia source: base/loading.jl:114-139; base/strings/basic.jl:257-263;
base/strings/substring.jl:252-283; base/strings/io.jl:42-54. -/
def ShowCorrect : Prop :=
  ∀ (allocation : Nat → JuliaLean.base.strings.string.StringAllocationOutcome)
      (initial : Nat → JuliaLean.base.pointer.Byte)
      (kind : Kind) (hash : SHA kind.width) (io : JIO Nat Unit) (failures : List Nat),
    hash.bytes.length = kind.width →
    let result := showDigest allocation initial probeCharIO io kind hash { failures := failures }
    let prefixSize := match kind with | .sha1 => 6 | .sha256 => 8
    match allocation prefixSize with
    | .outOfMemory =>
        result = .error (.string .outOfMemory) { failures := failures }
    | .allocated =>
        Emission (streamOf io)
          (fun output => ∃ digits, Encodes hash.bytes digits ∧ output =
            (match kind with | .sha1 => "SHA1(\"" | .sha256 => "SHA256(\"").toUTF8.toList ++
              digits ++ "\")".toUTF8.toList)
          result

end JuliaLean.Proofs.base.loading.Models1Group9.SHAIO
namespace JuliaLean.Proofs.base.loading.Models1Group9.SHAString

open JuliaLean
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group9.SHAString
open JuliaLean.base.strings.string (StringAllocationOutcome)

/-- Mathematical value of an ASCII lowercase hexadecimal digit. This does not
refer to the model's table, bit shifts, pointer heap or enumeration. -/
def digitValue (byte : UInt8) : Option Nat :=
  if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then some (byte.toNat - 48)
  else if 97 ≤ byte.toNat ∧ byte.toNat ≤ 102 then some (byte.toNat - 87)
  else none

/-- Independent positional encoding relation, including exact output length. -/
def Encodes (input output : List UInt8) : Prop :=
  output.length = 2 * input.length ∧
  ∀ (i : Nat) (byte : UInt8), input[i]? = some byte →
    ∃ high low highValue lowValue,
      output[2 * i]? = some high ∧ output[2 * i + 1]? = some low ∧
      digitValue high = some highValue ∧ digitValue low = some lowValue ∧
      byte.toNat = 16 * highValue + lowValue

/-- Both digest String methods produce exactly two lowercase hexadecimal digits
per byte, with no delimiters, from every possible fixed-width digest. The result
is independent of the fresh allocation's initial contents. OutOfMemoryError at
the actual requested size propagates, without a successful-run premise or an
assumed allocator correctness law. The only hypotheses restore the generated
NTuple{20/32,UInt8} field invariant. Runtime allocation decisions at all sizes
are quantified freely; the expected 40/64-byte request is mathematical.
Julia source: base/loading.jl:114-137; base/strings/util.jl:1286-1291,1316-1327;
base/strings/string.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def StringCorrect : Prop :=
  ∀ (allocation : Nat → StringAllocationOutcome) (initial : Nat → JuliaLean.base.pointer.Byte)
      (n : Nat) (hash : SHA n),
    (n = 20 ∨ n = 32) → hash.bytes.length = n →
    match allocation (2 * n) with
    | .allocated => ∃ output,
        stringDigest allocation initial hash = .ok output ∧ Encodes hash.bytes output.bytes
    | .outOfMemory => stringDigest allocation initial hash = .error .outOfMemory


end JuliaLean.Proofs.base.loading.Models1Group9.SHAString


namespace JuliaLean.Proofs.base.loading.Models1Group9

open JuliaLean JuliaLean.base.loading

/-- Independent positional value of a byte tuple, first byte most significant.
Used only in specifications, not by the SHA equality/ordering models. -/
def shaValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + shaValue bs

/-- Tuple-dispatched equality must return Bool, never missing or an exception,
and compare the complete digest value. Both SHA1 and SHA256 are included.
The only hypotheses are the actual NTuple field/type invariants.
Julia source: base/loading.jl:114-143; base/operators.jl:109-118. -/
def ShaEquality : Prop :=
  ∀ (ops : JuliaLean.base.tuple.Ops UInt8) (n : Nat) (a b : SHA n),
    (n = 20 ∨ n = 32) → a.bytes.length = n → b.bytes.length = n →
    JuliaLean.base.loading.Models1Group9.shaEqual ops a b =
      .ok (some (decide (shaValue a.bytes = shaValue b.bytes)))
end JuliaLean.Proofs.base.loading.Models1Group9
namespace JuliaLean.Proofs.base.loading.Models1Group9.SHAHash

open JuliaLean
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group9.SHAHash
open JuliaLean.base.hashing (Word)

/-- Complete-domain source invariant of the optional UInt64 seed mixing.
For each fixed digest and runtime type hash, different seeds give different
outputs: the source's xor operations and odd-multiplier UInt64 mixing are
permutations. This relation does not restate a hash fold or prescribe its
intermediate values. It detects omitting or truncating the seed.
The generated digest field length is the only representation hypothesis.
Source: base/loading.jl:142; base/tuple.jl:602-610;
base/hashing.jl:44-45,55-63,75-77. -/
def SeedInjective : Prop :=
  ∀ (runtimeTypeHash : Kind → Word)
      (byteOps : JuliaLean.base.tuple.Ops UInt8)
      (pairOps : JuliaLean.base.tuple.Ops (Kind ⊕ Bytes))
      (kind : Kind) (digest : SHA kind.width) (left right : Word),
    digest.bytes.length = kind.width →
    (hashDigest runtimeTypeHash byteOps pairOps kind digest left =
      hashDigest runtimeTypeHash byteOps pairOps kind digest right ↔ left = right)

/-- The documented hash/equality promise on all generated SHA values, including
independence from every unused tuple-interface field. Bytewise equality is
stated independently of the hash body. The two arbitrary existing interfaces
may differ in every unused field; their actual hash dispatch is concretely
bound by the model.
Source: base/hashing.jl:11-20; base/loading.jl:142-143. -/
def EqualBytesEqualHash : Prop :=
  ∀ (runtimeTypeHash : Kind → Word)
      (byteOps₁ byteOps₂ : JuliaLean.base.tuple.Ops UInt8)
      (pairOps₁ pairOps₂ : JuliaLean.base.tuple.Ops (Kind ⊕ Bytes))
      (kind : Kind) (left right : SHA kind.width) (seed : Word),
    left.bytes.length = kind.width → right.bytes.length = kind.width →
    (∀ i : Nat, i < kind.width → left.bytes[i]? = right.bytes[i]?) →
    hashDigest runtimeTypeHash byteOps₁ pairOps₁ kind left seed =
      hashDigest runtimeTypeHash byteOps₂ pairOps₂ kind right seed


end JuliaLean.Proofs.base.loading.Models1Group9.SHAHash


namespace JuliaLean.Proofs.base.loading.Models1Group9.Uuid5

open JuliaLean
open JuliaLean.base.loading.Models1Group9.Uuid5
open JuliaLean.base.uuid (UUID)
open JuliaLean.base.hashing (Word)
open JuliaLean.base.strings.string (JString)

/-- Independent source invariant: fake uuid5 always terminates successfully and
sets the version nibble to 5 and the variant's top two bits to binary 10.
All namespace UUIDs and all constructible Julia String bytes are quantified,
including invalid UTF-8 and embedded zero. The mathematical quotients extract
those bit fields without calling the model's masks or shifts. No property
claims cryptographic UUID5 compatibility; the source explicitly calls this fake.
Source: base/loading.jl:147-160. -/
def VersionVariant : Prop :=
  ∀ (ops : JuliaLean.base.tuple.Ops Word) (ns : UUID) (key : JString),
    ∃ result : UUID, uuid5 ops ns key = .ok result ∧
      (result.value.val.toNat / 2 ^ 76) % 16 = 5 ∧
      (result.value.val.toNat / 2 ^ 62) % 4 = 2

open JuliaLean.Registry


end JuliaLean.Proofs.base.loading.Models1Group9.Uuid5


namespace JuliaLean.Proofs.base.loading.Models1Group9.Slug

open JuliaLean
open JuliaLean.base.loading.Models1Group9.Slug

/-- Positional digit spelling independent of the String table and integer loop. -/
def digitCode (digit : Nat) : Nat :=
  if digit < 26 then 65 + digit
  else if digit < 52 then 97 + (digit - 26)
  else 48 + (digit - 52)

/-- Raw allocator outcomes sufficient for the single exact-capacity operation.
This is a predicate on supplied primitive outcomes, not a correctness law for
any constructor. Zero-byte String and Memory use shared singleton objects,
while the mutable IOBuffer header is still allocated. -/
def Allocated (allocation : Allocation) (p : JInt .i64) : Prop :=
  allocation.bufferHeader = .allocated ∧
    (0 < p.val → allocation.stringBytes p.val.toNat = .allocated ∧
      allocation.memoryHeader = .allocated)

/-- Complete allocation-aware output invariant for every UInt32 input, Int64
precision, raw allocator outcome and fresh-memory contents. Any required
allocation failure propagates as OutOfMemoryError. If the required allocations
succeed, output has exactly max(p,0) least-significant-first base62 digits.
Nonpositive precision still depends on allocation of the IOBuffer object.
Expected digits use mathematical powers and ASCII ranges, not the encoder.
Source: base/loading.jl:185-198; base/iobuffer.jl:96-107,246-270;
base/strings/string.jl:184-185,195. -/
def OutputInvariant : Prop :=
  ∀ (V Ty : Type) (allocation : Allocation) (initial : Nat → UInt8)
    (contextValues : JuliaLean.base.show.AnyOps V Ty)
    (displaySize : JInt .i64 × JInt .i64) (x : JInt .u32) (p : JInt .i64),
    (Allocated allocation p →
      ∃ output, slug allocation initial contextValues displaySize x p = .ok output ∧
        output.bytes.length = p.val.toNat ∧
        ∀ index : Nat, index < output.bytes.length →
          ∃ byte, output.bytes[index]? = some byte ∧
            byte.toNat = digitCode ((x.val.toNat / 62 ^ index) % 62)) ∧
    (¬ Allocated allocation p →
      slug allocation initial contextValues displaySize x p =
        .error (.callback (.string .outOfMemory)))

end JuliaLean.Proofs.base.loading.Models1Group9.Slug


namespace JuliaLean.Proofs.base.loading.Models1Group9.CRCSlugs

open JuliaLean
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group9.CRCSlugs

/-- Mathematical ASCII ranges of the package slug alphabet, independent of
its String table and the encoder's division/remainder implementation. -/
def IsDigit (byte : UInt8) : Prop :=
  (65 ≤ byte.toNat ∧ byte.toNat ≤ 90) ∨
  (97 ≤ byte.toNat ∧ byte.toNat ≤ 122) ∨
  (48 ≤ byte.toNat ∧ byte.toNat ≤ 57)

/-- Successful raw allocations for package_slug. This only inspects primitive
outcomes; it is not a correctness assumption about a Julia-level constructor. -/
def PackageAllocated (references : ReferenceAllocation)
    (allocation : JuliaLean.base.loading.Models1Group9.Slug.Allocation) (p : JInt64) : Prop :=
  references.uint128 = .allocated ∧
    JuliaLean.Proofs.base.loading.Models1Group9.Slug.Allocated allocation p

/-- Version_slug additionally allocates its private SHA1 tuple reference. -/
def VersionAllocated (references : ReferenceAllocation)
    (allocation : JuliaLean.base.loading.Models1Group9.Slug.Allocation) (p : JInt64) : Prop :=
  references.tuple = .allocated ∧ PackageAllocated references allocation p

/-- Independent output formatting and raw-allocation failure contract.
No encoder or checksum operation occurs in this predicate. Nonpositive widths
still require the source's RefValue and IOBuffer object allocations. -/
def Format (requiredAllocations : Prop) (p : JInt64)
    (result : Except (JuliaLean.base.strings.io.Error
      JuliaLean.base.loading.Models1Group9.Slug.OpError)
      JuliaLean.base.strings.io.JuliaString) : Prop :=
  (requiredAllocations →
    ∃ output, result = .ok output ∧
      output.bytes.length = p.val.toNat ∧ ∀ byte ∈ output.bytes, IsDigit byte) ∧
  (¬ requiredAllocations → result = .error (.callback (.string .outOfMemory)))

/-- Whole-domain package/version slug formatting. Every raw CRC result,
reference and buffer allocation outcome, fresh-memory byte and machine precision
is included. No runtime correctness law or success precondition is assumed.
SHA1's exact field length is its generated NTuple representation invariant.
Source: base/loading.jl:187-209; base/refvalue.jl:8. -/
def Formatting : Prop :=
  ∀ {V Ty : Type} (runtime : Runtime) (references : ReferenceAllocation)
      (allocation : JuliaLean.base.loading.Models1Group9.Slug.Allocation)
      (initial : Nat → UInt8)
      (contextValues : JuliaLean.base.show.AnyOps V Ty)
      (displaySize : JInt64 × JInt64) (uuid : JuliaLean.base.uuid.UUID)
      (sha1 : SHA 20) (p : JInt64),
    sha1.bytes.length = 20 →
    Format (PackageAllocated references allocation p) p
      (packageSlug runtime references allocation initial contextValues displaySize uuid p) ∧
    Format (VersionAllocated references allocation p) p
      (versionSlug runtime references allocation initial contextValues displaySize uuid sha1 p)

open JuliaLean.Registry


end JuliaLean.Proofs.base.loading.Models1Group9.CRCSlugs
namespace JuliaLean.Proofs.base.loading.Models1Group9.TOMLConstructor

open JuliaLean
open JuliaLean.base.loading.Models1Group9.TOMLConstructor

/-- Complete allocation-aware constructor ownership invariant. Successful
construction retains the input parser reference, preserves every old object,
and adds a fresh empty dictionary. Failure is exactly the raw Dict-header
OutOfMemoryError and leaves the heap unchanged. All primitive outcomes, payloads
and references are quantified; no constructor correctness law is assumed.
Source: base/loading.jl:290-294; base/dict.jl:77-82. -/
def SharesParserFreshEmptyDictionary : Prop :=
  ∀ (X D CI CF : Type)
      (allocation : JuliaLean.base.strings.string.StringAllocationOutcome)
      (parser : ParserRef X D CI CF) (before : Heap X D CI CF),
    match construct allocation parser before with
    | .error error after =>
        allocation = .outOfMemory ∧ error = .outOfMemory ∧ after = before
    | .ok cache after =>
        allocation = .allocated ∧ cache.parser = parser ∧
        after.parsers = before.parsers ∧ after.files = before.files ∧
        after.dictionaries.length = before.dictionaries.length + 1 ∧
        (∀ i, i < before.dictionaries.length →
          after.dictionaries[i]? = before.dictionaries[i]?) ∧
        before.dictionaries.length ≤ cache.dictionary.id ∧
        ∃ dictionary, after.dictionaries[cache.dictionary.id]? = some dictionary ∧
          dictionary.count = 0 ∧ dictionary.size = 0 ∧ dictionary.ndel = 0 ∧
          dictionary.age.val = 0 ∧
          (∀ i, dictionary.slots i = 0 ∧ dictionary.keys i = none ∧ dictionary.vals i = none)

/-- Every pair of raw allocation outcomes is covered. Two successful calls
share the parser and obtain distinct mutable dictionaries; a failed call throws
OutOfMemoryError without changing the heap visible before that call.
Source: base/loading.jl:294. -/
def SeparateDictionaryIdentities : Prop :=
  ∀ (X D CI CF : Type)
      (firstAllocation secondAllocation : JuliaLean.base.strings.string.StringAllocationOutcome)
      (parser : ParserRef X D CI CF) (before : Heap X D CI CF),
    match construct firstAllocation parser before with
    | .error error after =>
        firstAllocation = .outOfMemory ∧ error = .outOfMemory ∧ after = before
    | .ok first next =>
        firstAllocation = .allocated ∧
        match construct secondAllocation parser next with
        | .error error after =>
            secondAllocation = .outOfMemory ∧ error = .outOfMemory ∧ after = next
        | .ok second _ =>
            secondAllocation = .allocated ∧
            first.parser = second.parser ∧ first.dictionary ≠ second.dictionary

open JuliaLean.Registry


end JuliaLean.Proofs.base.loading.Models1Group9.TOMLConstructor
namespace JuliaLean.Proofs.base.loading.Models1Group9.StringVectorMembership

open JuliaLean
open JuliaLean.base.loading.Models1Group9.StringVectorMembership
open JuliaLean.base.strings.string (JString)
open JuliaLean.base.operators (Truth)

/-- An actual native String vector has a valid live window in a machine-sized
boxed-reference memory. The eight-byte cell bound is the installed generic-memory
allocator's native size limit. Unassigned slots are deliberately allowed; this
is a representation invariant, not an initialization precondition.
Source: base/loading.jl:783,1142; base/boot.jl:821-824. -/
def Constructible (heap : Heap) (vector : Nat) : Prop :=
  heap.validVector vector ∧
    ∃ header cells, heap.arrays[vector]? = some header ∧
      heap.memories[header.reference.1]? = some cells ∧
      cells.length * 8 < 2 ^ 63 - 2

/-- Every cell in this prior is assigned and differs in byte value. This
declarative prior relation does not execute the member/any/iterator models. -/
def NoMatch (slots : List (Option JString)) (name : JString) : Prop :=
  ∀ slot ∈ slots, ∃ value, slot = some value ∧ value.bytes ≠ name.bytes

/-- A matching assigned value occurs before any unassigned reference. Values
after that match, including unassigned cells, cannot affect the source result. -/
def MatchBeforeGap (slots : List (Option JString)) (name : JString) : Prop :=
  ∃ prior value suffix, slots = prior ++ some value :: suffix ∧
    value.bytes = name.bytes ∧ ∀ slot ∈ prior, slot.isSome = true

/-- The first unassigned cell is preceded only by assigned nonmatching values. -/
def GapBeforeMatch (slots : List (Option JString)) (name : JString) : Prop :=
  ∃ prior suffix, slots = prior ++ none :: suffix ∧ NoMatch prior name

/-- Full-domain membership invariant, including exact early UndefRefError.
Every constructible shared String vector terminates with true iff a matching
cell precedes a gap, false iff every cell is assigned and unequal, or UndefRefError
iff a gap precedes the first match. It accepts all native String bytes and does
not require initialized vectors, equal lengths, callback laws or success.
Source: base/loading.jl:783; base/operators.jl:1455; base/anyall.jl:120-132. -/
def MembershipOutcome : Prop :=
  ∀ (heap : Heap) (vector : Nat) (name : JString), Constructible heap vector →
    ∃ response : Except Error Truth,
      (extMayLoadWeakdep heap vector name).run = some response ∧
      match response with
      | .ok .true => MatchBeforeGap (heap.contents vector) name
      | .ok .false => NoMatch (heap.contents vector) name
      | .error (.inl .undefinedReference) => GapBeforeMatch (heap.contents vector) name
      | _ => False

/-- Full-domain dependency lookup invariant. A matching value before any gap
returns exactly the requested name with no UUID; absence returns nothing, and
an earlier unassigned reference throws UndefRefError. Expected results use only
the independent positional prior predicates above, not the membership body.
Source: base/loading.jl:1142-1145; base/pkgid.jl:8,10. -/
def DependencyOutcome : Prop :=
  ∀ (heap : Heap) (vector : Nat) (name : JString), Constructible heap vector →
    ∃ response : Except Error (Option JuliaLean.base.pkgid.PkgId),
      (depStanzaGet heap vector name).run = some response ∧
      match response with
      | .ok (some package) =>
          package.uuid = none ∧ package.name = name.bytes ∧
          MatchBeforeGap (heap.contents vector) name
      | .ok none => NoMatch (heap.contents vector) name
      | .error (.inl .undefinedReference) => GapBeforeMatch (heap.contents vector) name
      | _ => False

end JuliaLean.Proofs.base.loading.Models1Group9.StringVectorMembership
namespace JuliaLean.Proofs.base.loading.Models1Group9

open JuliaLean JuliaLean.base.loading
open JuliaLean.base.pkgid (PkgId)
open JuliaLean.base.toml.parser (Val)

/-- A concrete protocol observation adapter for the existing CacheFetchOps
boundary. For this observation only, World.loading_extension stores the hook's
TLS guard bit; it is not an installed TLS implementation or a claim that Julia
shares these two variables. Hook and logger actions are arbitrary, including
exceptions, divergence and state mutations. The bit is checked after each
finite call, so this specification is sensitive to misplaced finally blocks.
Source: base/loading.jl:1720-1735 (TLS guard and cleanup invariant). -/
def cacheFetchProbe {X Y E D CI CF V : Type}
    (o : LOps X Y E D CI CF V) (hookAvailable generating : Bool)
    (hookAction : LM o (Val X)) (loggerAction : LErr E → LM o Unit) :
    CacheFetchOps o Unit where
  hook := pure (if hookAvailable then some () else none)
  generatingOutput := pure generating
  hasInCacheFetchHook := do return (← getW o).loading_extension
  setInCacheFetchHook := modifyW o fun w => { w with loading_extension := true }
  deleteInCacheFetchHook := modifyW o fun w => { w with loading_extension := false }
  invokeLatest := fun _ _ _ => hookAction
  logDebugFailure := fun _ err => loggerAction err

/-- Skipped calls return false without running hook/logger actions or changing
state. Entered calls clear the TLS guard on every finite exit, even when the
hook or error logger throws. Availability, output generation and the initial
reentrancy bit range over all possibilities. Hook and logger actions are arbitrary;
no success, correctness or purity law is assumed. Divergence has no completed
finally obligation. Julia source/documentation: base/loading.jl:1688-1735. -/
def CacheFetchCleanup : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V)
    (hookAvailable generating : Bool)
    (hookAction : LM o (Val X)) (loggerAction : LErr E → LM o Unit)
    (pkg : PkgId) (sourcePath : Bytes) (w : World X D CI CF),
    let result := (JuliaLean.base.loading.maybe_fetch_cache o
      (cacheFetchProbe o hookAvailable generating hookAction loggerAction)
      pkg sourcePath).run.run w
    if hookAvailable = false ∨ generating = true ∨ w.loading_extension = true then
      result = some (.ok false, w)
    else match result with
      | none => True
      | some (_, finalWorld) => finalWorld.loading_extension = false

end JuliaLean.Proofs.base.loading.Models1Group9
namespace JuliaLean.Proofs.base.loading.Models1Group9.Flags

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.loading (CacheFlags)

/-- Positional binary digits of a 64-bit signed machine integer, interpreted as
a word. This is a mathematical specification, not a machine operation. -/
def wordBit (value : JInt .i64) (bit : Nat) : Prop :=
  ((value.val % (2 : Int)^64).toNat / 2^bit) % 2 = 1

/-- A destination bit is present when any stored field contributes that bit.
The union formulation permits overlapping, negative, and large field values;
it imposes no undocumented small-field premise. -/
def destinationBit (cf : CacheFlags) (bit : Nat) : Prop :=
  (bit = 0 ∧ cf.use_pkgimages = true) ∨
  (1 ≤ bit ∧ wordBit cf.debug_level (bit - 1)) ∨
  (3 ≤ bit ∧ wordBit cf.check_bounds (bit - 3)) ∨
  (bit = 5 ∧ cf.inline = true) ∨
  (6 ≤ bit ∧ wordBit cf.opt_level (bit - 6))

instance (cf : CacheFlags) (bit : Nat) : Decidable (destinationBit cf bit) :=
  inferInstanceAs (Decidable
    ((bit = 0 ∧ cf.use_pkgimages = true) ∨
      (1 ≤ bit ∧ ((cf.debug_level.val % (2 : Int)^64).toNat / 2^(bit - 1)) % 2 = 1) ∨
      (3 ≤ bit ∧ ((cf.check_bounds.val % (2 : Int)^64).toNat / 2^(bit - 3)) % 2 = 1) ∨
      (bit = 5 ∧ cf.inline = true) ∨
      (6 ≤ bit ∧ ((cf.opt_level.val % (2 : Int)^64).toNat / 2^(bit - 6)) % 2 = 1)))

/-- Independent positional magnitude of the union of the 64 destination bits. -/
def packedMagnitude (cf : CacheFlags) : Nat :=
  ((List.range 64).map fun bit => if destinationBit cf bit then 2^bit else 0).sum

/-- Invariant for the complete Int64 constructor domain: a representable input
is decoded into its positional digit fields with no coverage, and an input
outside the byte range raises InexactError. Julia source: base/loading.jl:1971-1979.
The expected fields are arithmetic digits, not copies of the bitwise model body.
No success premise or input restriction is imposed. -/
def IntConstructorCorrect : Prop :=
  ∀ flags : JInt .i64,
    match JuliaLean.base.loading.Models1Group9.Flags.fromInt flags with
    | .ok cf =>
        0 ≤ flags.val ∧ flags.val < 256 ∧
        cf.use_pkgimages = decide (flags.val % 2 = 1) ∧
        cf.debug_level.val = (flags.val / 2) % 4 ∧
        cf.check_bounds.val = (flags.val / 8) % 4 ∧
        cf.inline = decide ((flags.val / 32) % 2 = 1) ∧
        cf.opt_level.val = (flags.val / 64) % 4 ∧
        cf.coverage.val = 0 ∧ cf.coverage_path = none
    | .error (.inexactError _) => flags.val < 0 ∨ 256 ≤ flags.val
    | .error _ => False

/-- Restore the machine-sized String representation invariant of the optional
coverage_path field (base/loading.jl:1967). This does not constrain flag values. -/
def ConstructibleCacheFlags (cf : CacheFlags) : Prop :=
  match cf.coverage_path with
  | none => True
  | some path => path.length ≤ 2^63 - 1

/-- Invariant for every constructible CacheFlags value: encoding equals the positional
union of the source field bits if it fits a byte, and otherwise raises
InexactError. Julia source: base/loading.jl:2012-2020; integer wrapping semantics:
doc/src/manual/integers-and-floating-point-numbers.md:231-249.
The specification covers negative fields, shifted-out high bits, overlaps,
coverage values, and every represented coverage path; no field-range premise
is used. The sole premise bounds the stored String to the machine-size domain.
Encoding never examines or allocates the path bytes. -/
def ByteEncodingCorrect : Prop :=
  ∀ cf : CacheFlags, ConstructibleCacheFlags cf →
    match JuliaLean.base.loading.Models1Group9.Flags.toUInt8 cf with
    | .ok byte => packedMagnitude cf < 256 ∧ byte.val = (packedMagnitude cf : Int)
    | .error (.inexactError _) => 256 ≤ packedMagnitude cf
    | .error _ => False

end JuliaLean.Proofs.base.loading.Models1Group9.Flags
namespace JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageMemory

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.loading.Models1Group9.CurrentCoverageMemory
open JuliaLean.base.pointer (Ptr)
open JuliaLean.base.strings.string (CStringPrefix StringAllocationOutcome)

/-- Independent observations of the two ABI fields, expressed as unsigned
memory bytes rather than the model's signed field decoding and promoted eq.
Source: base/options.jl:26,28; base/loading.jl:2006. -/
def PathMode (runtime : Runtime) : Prop :=
  (runtime.strings.heap.readByte
    (runtime.optionsAddress.address.val.toNat + 101)).val = 3 ∧
  (runtime.strings.heap.readByte
    (runtime.optionsAddress.address.val.toNat + 103)).val = 0

/-- Independent mathematical little-endian address value, without the model's
UInt64 shifts, bit-or fold or loaded image decoder. Source: base/options.jl:29. -/
def Address (runtime : Runtime) : Nat :=
  ((List.range 8).map (fun i =>
    (runtime.strings.heap.readByte
      (runtime.optionsAddress.address.val.toNat + 104 + i)).val.toNat * 256 ^ i)).sum

def SpecPointer (runtime : Runtime) : Ptr (JInt .u8) :=
  ⟨JInt.wrap .u64 (Int.ofNat (Address runtime))⟩

/-- A direct positional copy of the first-NUL prefix in the source memory.
This does not call a String constructor, pointer load or the model's copy body. -/
def CopiesPrefix (runtime : Runtime) (length : Nat) (bytes : List UInt8) : Prop :=
  bytes.length = length ∧
  ∀ i : Nat, i < length → ∃ byte,
    bytes[i]? = some byte ∧
    byte.toNat = (runtime.strings.heap.readByte (Address runtime + i)).val.toNat

/-- Actual allocator refusal, including the installed C size-overflow guard.
A zero-length C string returns the shared empty String and ignores the allocator.
Source: src/array.c:283-310 through the supplied StringPointerPrimitive model. -/
def AllocationRefused (runtime : Runtime) (length : Nat) : Prop :=
  length ≠ 0 ∧
    (2 ^ 64 - 10 < length ∨
      runtime.strings.allocateString length = StringAllocationOutcome.outOfMemory)

/-- Exhaustive public behavior, independently specified from physical input
fields and the first-NUL memory relation. All option bytes, native pointer values,
C-memory states and existing allocation/strlen primitive outcomes are quantified.
Disabled path coverage returns nothing even if tracked_path is null or invalid;
selected null pointers raise ArgumentError; readable prefixes are copied exactly
or fail at allocation; undefined C memory is retained rather than forged into a
Julia error. No high-level options/string callback law is a premise.
Source: base/loading.jl:2004-2008; base/options.jl:4-85;
base/strings/string.jl:176-179. -/
def CompleteOutcome : Prop :=
  ∀ runtime : Runtime,
    match currentCoveragePath runtime with
    | .error _ => False
    | .ok (.success none) => ¬ PathMode runtime
    | .ok (.success (some bytes)) =>
        PathMode runtime ∧ Address runtime ≠ 0 ∧
        ∃ region : CStringPrefix runtime.strings.heap (SpecPointer runtime),
          ¬ AllocationRefused runtime region.length ∧
          CopiesPrefix runtime region.length bytes
    | .ok (.juliaError (.jl (.argumentError _))) =>
        PathMode runtime ∧ Address runtime = 0
    | .ok (.juliaError .outOfMemory) =>
        PathMode runtime ∧ Address runtime ≠ 0 ∧
        ∃ region : CStringPrefix runtime.strings.heap (SpecPointer runtime),
          AllocationRefused runtime region.length
    | .ok .undefinedMemory =>
        PathMode runtime ∧ Address runtime ≠ 0 ∧
        ¬ ∃ _region : CStringPrefix runtime.strings.heap (SpecPointer runtime), True
    | .ok (.juliaError _) => False


end JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageMemory


namespace JuliaLean.Proofs.base.loading.Models1Group9.CacheFlagOptions

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group9.CacheFlagOptions
open JuliaLean.base.loading.Models1Group9.CurrentCoverageMemory (Runtime)
open JuliaLean.base.strings.string (CStringPrefix)
open JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageMemory

/-- Independent per-field override promises. Nonzero coverage uses the selected
path; zero coverage clears it. Conditions inspect the caller's keyword values,
not the model's getD/update implementation. Source: base/loading.jl:1989-1998. -/
def Fields (overrides : Overrides) (original result : CacheFlags) : Prop :=
  (overrides.use_pkgimages = none → result.use_pkgimages = original.use_pkgimages) ∧
  (∀ value, overrides.use_pkgimages = some value → result.use_pkgimages = value) ∧
  (overrides.debug_level = none → result.debug_level = original.debug_level) ∧
  (∀ value, overrides.debug_level = some value → result.debug_level = value) ∧
  (overrides.check_bounds = none → result.check_bounds = original.check_bounds) ∧
  (∀ value, overrides.check_bounds = some value → result.check_bounds = value) ∧
  (overrides.inline = none → result.inline = original.inline) ∧
  (∀ value, overrides.inline = some value → result.inline = value) ∧
  (overrides.opt_level = none → result.opt_level = original.opt_level) ∧
  (∀ value, overrides.opt_level = some value → result.opt_level = value) ∧
  (overrides.coverage = none → result.coverage = original.coverage) ∧
  (∀ value, overrides.coverage = some value → result.coverage = value) ∧
  (result.coverage.val = 0 → result.coverage_path = none) ∧
  (result.coverage.val ≠ 0 →
    (overrides.coverage_path = none → result.coverage_path = original.coverage_path) ∧
    (overrides.coverage_path = some none → result.coverage_path = none) ∧
    (∀ path, overrides.coverage_path = some (some path) →
      result.coverage_path = some path.bytes))

/-- All explicit cf values and keyword combinations are accepted, including
negative and extreme Int64 flags. No default runtime action is evaluated, and
the output obeys every field override and zero-coverage path clearing rule.
Source: base/loading.jl:1980-1999. -/
def ExplicitInput : Prop :=
  ∀ (X Y E D CI CF V : Type)
    (o : LOps X Y E D CI CF V) (cacheRuntime : CacheFlagsRuntimeOps o)
    (coverageRuntime : CoverageOps o) (options : Runtime)
    (input : Input) (overrides : Overrides) (world : World X D CI CF),
    ∃ result : CacheFlags,
      (withOptions o cacheRuntime coverageRuntime options (some input) overrides).run.run world =
        some (.ok (.ok (.success result)), world) ∧
      Fields overrides input.flags result

/-- Independent arithmetic decoding of the runtime byte and the inner source2000
constructor's path rule. It uses division/remainders of mathematical naturals,
not source shifts/masks or any constructor call. The inner coverage0 clearing
is observed before the outer keyword override, which may change coverage again.
Source: base/loading.jl:1971-1978,2000-2001. -/
def DefaultFields (flags coverage : JInt .u8) (path : Option Bytes) : CacheFlags where
  use_pkgimages := decide (flags.val.toNat % 2 = 1)
  debug_level := JInt.wrap .i64 (Int.ofNat ((flags.val.toNat / 2) % 4))
  check_bounds := JInt.wrap .i64 (Int.ofNat ((flags.val.toNat / 8) % 4))
  inline := decide ((flags.val.toNat / 32) % 2 = 1)
  opt_level := JInt.wrap .i64 (Int.ofNat ((flags.val.toNat / 64) % 4))
  coverage := JInt.wrap .i64 coverage.val
  coverage_path := if coverage.val = 0 then none else path

/-- Full default-argument protocol. Arbitrary C actions are observed in their
actual sequence, preserving intermediate/final state, exceptions and divergence.
Only after both succeed does the independent physical-memory/path specification
apply. Successful defaults are decoded mathematically and then constrained by
the independent keyword-field promises above. No callee-correctness premise is
supplied, and no public error branch or numeric/keyword input is excluded.
Source: base/loading.jl:1980-2001; base/options.jl:85;
base/strings/string.jl:176-179. -/
def DefaultInput : Prop :=
  ∀ (X Y E D CI CF V : Type)
    (o : LOps X Y E D CI CF V) (cacheRuntime : CacheFlagsRuntimeOps o)
    (coverageRuntime : CoverageOps o) (options : Runtime)
    (overrides : Overrides) (world : World X D CI CF),
    let observed := (withOptions o cacheRuntime coverageRuntime options none overrides).run.run world
    match cacheRuntime.jlCacheFlags.run.run world with
    | none => observed = none
    | some (.error error, next) => observed = some (.error error, next)
    | some (.ok flags, afterFlags) =>
        match coverageRuntime.imageCoverageConfig.run.run afterFlags with
        | none => observed = none
        | some (.error error, next) => observed = some (.error error, next)
        | some (.ok coverage, afterCoverage) =>
            let successful := fun path : Option Bytes =>
              ∃ result : CacheFlags,
                observed = some (.ok (.ok (.success result)), afterCoverage) ∧
                Fields overrides (DefaultFields flags coverage path) result
            (¬ PathMode options → successful none) ∧
            (PathMode options → Address options = 0 →
              ∃ message : String,
                observed = some (.ok (.ok (.juliaError (.jl (.argumentError message)))),
                  afterCoverage)) ∧
            (PathMode options → Address options ≠ 0 →
              ((¬ ∃ _region : CStringPrefix options.strings.heap (SpecPointer options), True) →
                observed = some (.ok (.ok .undefinedMemory), afterCoverage)) ∧
              (∀ region : CStringPrefix options.strings.heap (SpecPointer options),
                (AllocationRefused options region.length →
                  observed = some (.ok (.ok (.juliaError .outOfMemory)), afterCoverage)) ∧
                (¬ AllocationRefused options region.length →
                  ∃ bytes, CopiesPrefix options region.length bytes ∧ successful (some bytes))))


end JuliaLean.Proofs.base.loading.Models1Group9.CacheFlagOptions


namespace JuliaLean.Proofs.base.loading.Models1Group9.Coverage

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.loading

/-- The optional String field must have a Julia machine-representable byte
length. No constraint is placed on any of the integer flags.
Julia source: base/loading.jl:1967. -/
def ConstructibleFlags (flags : CacheFlags) : Prop :=
  match flags.coverage_path with
  | none => True
  | some path => path.length ≤ 2^63 - 1

/-- An unrepresentable coverage value raises InexactError without changing
state, for every possible action at the C-call boundary, including actions
that throw or diverge. This independently states the checked-argument
invariant of base/loading.jl:2044-2046; it assumes no correctness law about
the runtime matcher. All other flag fields range over their full domain.
The path-length premises restore only the Julia String representation bound. -/
def RejectsInvalidCoverageWithoutEffects : Prop :=
  ∀ (X Y E D CI CF V : Type)
    (o : LOps X Y E D CI CF V) (ops : CoverageOps o)
    (requested actual : CacheFlags) (world : World X D CI CF),
    ConstructibleFlags requested → ConstructibleFlags actual →
    (requested.coverage.val < 0 ∨ 255 < requested.coverage.val ∨
      actual.coverage.val < 0 ∨ 255 < actual.coverage.val) →
    ∃ name : String,
      (JuliaLean.base.loading.Models1Group9.Coverage.matchCacheCoverage
        o ops requested actual).run.run.run world =
      some (.ok (.error (.inexactError name)), world)

end JuliaLean.Proofs.base.loading.Models1Group9.Coverage
namespace JuliaLean.Proofs.base.loading.Models1Group9.CoverageOptions

open JuliaLean
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group9
open JuliaLean.base.loading.Models1Group9.CoverageOptions
open JuliaLean.base.pointer (Byte)

/-- Independent source allocation schedule. Sizes are mathematical byte/cell
counts derived from the literal widths and input path, rather than calls to
the builder, array allocator or target method. Source: base/loading.jl:2036-2041. -/
def RequiredAllocations (input : CacheFlagOptions.Input) : List AllocationEvent :=
  if input.flags.coverage.val = 0 then
    [⟨.vectorMemory, 1⟩, ⟨.vectorHeader, 0⟩]
  else
    (match input.flags.coverage_path with
      | none => []
      | some path => [⟨.scope, path.length + 1⟩]) ++
    [⟨.coverageArgument, 16 +
        (match input.flags.coverage_path with | none => 4 | some path => path.length + 1)⟩,
     ⟨.modeArgument, if input.flags.coverage.val = 2 then 26 else 24⟩,
     ⟨.vectorMemory, 2⟩, ⟨.vectorHeader, 0⟩]

/-- A positional byte segment. This mathematical relation invokes no String
builder, copying primitive, array operation or coverage method.
Source: the command-line byte promise of base/loading.jl:2036-2041. -/
def BytesAt (bytes : Bytes) (offset : Nat) (expected : Bytes) : Prop :=
  ∀ i, i < expected.length → bytes[offset + i]? = expected[i]?

/-- Independent positional command-line specification. It fixes the number
of assigned arguments, their lengths, literal prefixes and each path byte's
position, without invoking either the old or new coverage_cache_options body.
Source: base/loading.jl:2036-2041. -/
def CommandBytes (input : CacheFlagOptions.Input) (cells : List (Option Bytes)) : Prop :=
  if input.flags.coverage.val = 0 then
    ∃ argument, cells = [some argument] ∧ argument.length = 20 ∧
      BytesAt argument 0 (lit "--code-coverage=none")
  else
    ∃ first second, cells = [some first, some second] ∧
      BytesAt first 0 (lit "--code-coverage=") ∧
      (match input.flags.coverage_path with
        | none => first.length = 20 ∧ BytesAt first 16 (lit "user")
        | some path => first.length = 17 + path.length ∧
            first[16]? = some 64 ∧ BytesAt first 17 path) ∧
      BytesAt second 0 (lit "--code-coverage-mode=") ∧
      (if input.flags.coverage.val = 2 then
        second.length = 26 ∧ BytesAt second 21 (lit "count")
       else second.length = 24 ∧ BytesAt second 21 (lit "hit"))

/-- Every successful call returns a fresh mutable String vector with the
independently specified command-line byte positions, while preserving all old
memories/headers. All native CacheFlags fields, all path bytes, all raw outcomes
and arbitrary fresh storage are quantified.
Source: base/loading.jl:2036-2041; base/array.jl:159-166. -/
def FreshCommandVector : Prop :=
  ∀ (allocation : Allocation) (initial : AllocationSite → Nat → Byte)
      (input : CacheFlagOptions.Input) (before : State),
    match coverageCacheOptions allocation initial input before with
    | .error _ after =>
        after.vectors.arrays = before.vectors.arrays ∧
        (∀ i, i < before.vectors.memories.length →
          after.vectors.memories[i]? = before.vectors.memories[i]?)
    | .ok vector after =>
        vector = before.vectors.arrays.length ∧
        after.vectors.arrays.length = before.vectors.arrays.length + 1 ∧
        after.vectors.memories.length = before.vectors.memories.length + 1 ∧
        after.vectors.validVector vector ∧
        (∀ i, i < before.vectors.arrays.length →
          after.vectors.arrays[i]? = before.vectors.arrays[i]?) ∧
        (∀ i, i < before.vectors.memories.length →
          after.vectors.memories[i]? = before.vectors.memories[i]?) ∧
        CommandBytes input (after.vectors.contents vector)

/-- Full-domain allocation and exception precedence, including disabled
coverage and absent paths. Success reaches exactly the source's required raw
sites and has every required outcome allocated. Failure is OutOfMemoryError
at the first refused site; neither later outcomes nor a later vector header
are reached. An earlier Memory remains present when only its subsequent Array
header fails. No allocator-correctness or success premise is assumed.
Source: base/loading.jl:2036-2041; base/boot.jl:821-824;
base/strings/substring.jl:256-283. -/
def AllocationOrderAndErrors : Prop :=
  ∀ (allocation : Allocation) (initial : AllocationSite → Nat → Byte)
      (input : CacheFlagOptions.Input) (before : State),
    match coverageCacheOptions allocation initial input before with
    | .ok _ after =>
        after.allocations = before.allocations ++ RequiredAllocations input ∧
        ∀ event ∈ RequiredAllocations input,
          allocation event.site event.size = .allocated
    | .error error after =>
        error = .string .outOfMemory ∧
        ∃ prior refused later,
          RequiredAllocations input = prior ++ refused :: later ∧
          (∀ event ∈ prior, allocation event.site event.size = .allocated) ∧
          allocation refused.site refused.size = .outOfMemory ∧
          after.allocations = before.allocations ++ prior ++ [refused] ∧
          after.vectors.arrays = before.vectors.arrays ∧
          (if refused.site = .vectorHeader then
            after.vectors.memories = before.vectors.memories ++
              [List.replicate (if input.flags.coverage.val = 0 then 1 else 2) none]
           else after.vectors.memories = before.vectors.memories)

/-- Mutable result identity is independent of equal command-line contents.
Two successful calls return different vector objects, and constructing the
second leaves the first object's live cells intact. All intervening primitive
allocation failures are included by quantifying both runs and case-splitting
their outcomes; they are not assumptions on the input domain.
Source: base/loading.jl:2036-2041; base/array.jl:159-166. -/
def SeparateResultIdentities : Prop :=
  ∀ (firstAllocation secondAllocation : Allocation)
      (firstInitial secondInitial : AllocationSite → Nat → Byte)
      (firstInput secondInput : CacheFlagOptions.Input) (before : State),
    match coverageCacheOptions firstAllocation firstInitial firstInput before with
    | .error _ _ => True
    | .ok first middle =>
        match coverageCacheOptions secondAllocation secondInitial secondInput middle with
        | .error _ _ => True
        | .ok second after =>
            first ≠ second ∧ after.vectors.contents first = middle.vectors.contents first

open JuliaLean.Registry


end JuliaLean.Proofs.base.loading.Models1Group9.CoverageOptions


namespace JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageRequest

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group9.CurrentCoverageRequest
open JuliaLean.base.loading.Models1Group9.CurrentCoverageMemory (Runtime)
open JuliaLean.base.strings.string (CStringPrefix)
open JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageMemory

/-- Independent path match: the requested String has the first-NUL prefix's
length and the same byte at every position. This does not call a String equality
or model conversion. Source: base/loading.jl:2063. -/
def PathMatches (path : Bytes) (runtime : Runtime)
    (region : CStringPrefix runtime.strings.heap (SpecPointer runtime)) : Prop :=
  path.length = region.length ∧
  ∀ i, i < region.length → ∃ byte,
    path[i]? = some byte ∧
    byte.toNat = (runtime.strings.heap.readByte (Address runtime + i)).val.toNat

/-- Full-domain, effect-aware contract. Absent requested paths and disabled
path coverage return false without querying the image runtime. A selected null,
invalid or allocation-failing C string preserves its distinct source outcome.
An unequal path also returns false without effects. Exactly matched paths retain
the raw image-query action's error/state/divergence and compare its byte result
with the unrestricted Int64 coverage request using mathematical integer equality.
All options bytes, valid global states, raw runtime outcomes, requested String
contents (including NUL/invalid UTF-8), and all other CacheFlags fields are included.
Source: base/loading.jl:2062-2064; base/options.jl:85;
base/strings/string.jl:176-179,238. -/
def CompleteOutcome : Prop :=
  ∀ (X Y E D CI CF V : Type)
    (o : LOps X Y E D CI CF V) (ops : CoverageOps o)
    (runtime : Runtime) (requested : Request) (world : World X D CI CF),
    let observed := (isCurrentCoverageRequest o ops runtime requested).run.run world
    ((requested.flags.coverage_path = none ∨ ¬ PathMode runtime) →
      observed = some (.ok (.ok (.success false)), world)) ∧
    (∀ path, requested.flags.coverage_path = some path →
      (PathMode runtime → Address runtime = 0 →
        ∃ message : String,
          observed = some (.ok (.ok (.juliaError (.jl (.argumentError message)))), world)) ∧
      (PathMode runtime → Address runtime ≠ 0 →
        ((¬ ∃ _region : CStringPrefix runtime.strings.heap (SpecPointer runtime), True) →
          observed = some (.ok (.ok .undefinedMemory), world)) ∧
        (∀ region : CStringPrefix runtime.strings.heap (SpecPointer runtime),
          (AllocationRefused runtime region.length →
            observed = some (.ok (.ok (.juliaError .outOfMemory)), world)) ∧
          (¬ AllocationRefused runtime region.length →
            ((¬ PathMatches path runtime region) →
              observed = some (.ok (.ok (.success false)), world)) ∧
            (PathMatches path runtime region →
              observed = (ops.imageCoverageConfig.run.run world).map
                (fun (result, finalWorld) =>
                  (result.map (fun code => .ok (.success
                    (decide (requested.flags.coverage.val = code.val)))), finalWorld)))))))


end JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageRequest


namespace JuliaLean.Proofs.base.loading.Models1Group9.PlainCoverage

open JuliaLean
open JuliaLean.base.loading

/-- Independent positional word specification for base/loading.jl:2067-2070.
The first word contains source bits64-127 and the second contains bits0-63.
Int division and remainder here describe mathematics in a Prop; they are
not the implementation's machine operations. No shift or conversion model
occurs in this specification. -/
def WordPositions (buildId : JInt .u128) (high low : JInt .u64) : Prop :=
  ∀ i : Fin 64,
    (high.val / (2 : Int) ^ i.val) % 2 =
      (buildId.val / (2 : Int) ^ (i.val + 64)) % 2 ∧
    (low.val / (2 : Int) ^ i.val) % 2 =
      (buildId.val / (2 : Int) ^ i.val) % 2

/-- Both wrappers pass the independently specified high/low word positions
to their existing C boundaries, including zero, the native maximum and every
other UInt128 input. An observing boundary reports the actual arguments in
its error payload, so swapped, truncated, omitted or wrongly shifted words
remain visible. This is a test of the actual caller, not a premise asserting
that a supplied callback performs its Julia callee correctly. The observation
also requires propagation of the exact boundary error and unchanged world.
Source: base/loading.jl:2067-2070. -/
def PassesWordsPositionally : Prop :=
  ∀ (X Y D CI CF V : Type)
      (o : LOps X Y (JInt .u64 × JInt .u64) D CI CF V)
      (ops : CoverageOps o) (buildId : JInt .u128)
      (world : World X D CI CF),
    ∃ high low : JInt .u64,
      WordPositions buildId high low ∧
      (JuliaLean.base.loading.Models1Group9.PlainCoverage.acceptPlainCoverageCache
        o { ops with acceptPlainCoverageCache := fun first second => throwL o (.ext (first, second)) }
        buildId).run.run world =
        some (.error (.ext (high, low)), world) ∧
      (JuliaLean.base.loading.Models1Group9.PlainCoverage.plainCoverageCacheAccepted
        o { ops with plainCoverageCacheAccepted := fun first second => throwL o (.ext (first, second)) }
        buildId).run.run world =
        some (.error (.ext (high, low)), world)

/-- For every stateful action at the existing acceptance C boundary, the
wrapper preserves the complete observed result: success, exact runtime error,
final world and divergence. Quantification over arbitrary stateful actions
can expose an added call, a caught error or an extra state update; no successful
runtime outcome or boundary-correctness law is assumed. Argument values are
independently checked by PassesWordsPositionally.
Source: base/loading.jl:2067-2068. -/
def PreservesAcceptanceOutcome : Prop :=
  ∀ (X Y E D CI CF V : Type)
      (o : LOps X Y E D CI CF V) (ops : CoverageOps o)
      (action : LM o Unit) (buildId : JInt .u128)
      (world : World X D CI CF),
    (JuliaLean.base.loading.Models1Group9.PlainCoverage.acceptPlainCoverageCache
      o { ops with acceptPlainCoverageCache := fun _ _ => action }
      buildId).run.run world = action.run.run world

/-- The query preserves either Boolean return value, every runtime error,
the complete final world and divergence from its existing normalized C
boundary. The property quantifies an arbitrary stateful boundary action and
every UInt128 input, with no success or ordinary-value restriction.
Source: base/loading.jl:2069-2070. -/
def PreservesQueryOutcome : Prop :=
  ∀ (X Y E D CI CF V : Type)
      (o : LOps X Y E D CI CF V) (ops : CoverageOps o)
      (action : LM o Bool) (buildId : JInt .u128)
      (world : World X D CI CF),
    (JuliaLean.base.loading.Models1Group9.PlainCoverage.plainCoverageCacheAccepted
      o { ops with plainCoverageCacheAccepted := fun _ _ => action }
      buildId).run.run world = action.run.run world

end JuliaLean.Proofs.base.loading.Models1Group9.PlainCoverage

namespace JuliaLean.Proofs.base.loading

open JuliaLean.Registry

open JuliaLean JuliaLean.base.loading

private theorem wrap_i64_zero : wrapInt .i64 0 = 0 :=
  wrapInt_of_inRange .i64 0 (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])

private theorem wrap_i64_five : wrapInt .i64 5 = 5 :=
  wrapInt_of_inRange .i64 5 (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])

private theorem wrap_u64_zero : wrapInt .u64 0 = 0 :=
  wrapInt_of_inRange .u64 0 (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])

private theorem lit_i64_zero_val : (JInt.lit .i64 0).val = 0 := wrap_i64_zero
private theorem int_lit_i64_zero_val : (JuliaLean.base.int.lit .i64 0).val = 0 := wrap_i64_zero
private theorem lit_i64_five_val : (JInt.lit .i64 5).val = 5 := wrap_i64_five

private theorem eqSame_int_lit_i64_zero (x : JInt .i64) :
    JuliaLean.base.int.eqSame x (JuliaLean.base.int.lit .i64 0) = decide (x.val = 0) := by
  unfold JuliaLean.base.int.eqSame
  rw [JuliaLean.Proofs.base.int.eq_int_eq, int_lit_i64_zero_val]

private theorem eq_i32_i64_zero (x : JInt .i32) :
    JuliaLean.base.int.eq x (JInt.lit .i64 0) = decide (x.val = 0) := by
  rw [JuliaLean.Proofs.base.int.eq_eq, lit_i64_zero_val]

private theorem lm_bind_run {X Y E D CI CF V α β : Type} {o : LOps X Y E D CI CF V}
    (act : LM o α) (f : α → LM o β) (w : World X D CI CF) :
    StateT.run (ExceptT.run (act >>= f)) w =
      match StateT.run (ExceptT.run act) w with
      | none => none
      | some (.error e, w') => some (.error e, w')
      | some (.ok a, w') => StateT.run (ExceptT.run (f a)) w' := by
  simp only [ExceptT.run, StateT.run, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    StateT.bind, Option.bind]
  cases act w with
  | none => rfl
  | some p => rcases p with ⟨r, w'⟩; cases r <;> rfl

private theorem lm_pure_run {X Y E D CI CF V α : Type} {o : LOps X Y E D CI CF V}
    (a : α) (w : World X D CI CF) :
    StateT.run (ExceptT.run (pure a : LM o α)) w = some (.ok a, w) := rfl

private theorem lm_tryFinally_run {X Y E D CI CF V α : Type} {o : LOps X Y E D CI CF V}
    (body : LM o α) (cleanup : LM o Unit) (w : World X D CI CF) :
    StateT.run (ExceptT.run (tryFinallyL o body cleanup)) w =
      match StateT.run (ExceptT.run body) w with
      | none => none
      | some (res, w1) =>
          match StateT.run (ExceptT.run cleanup) w1 with
          | none => none
          | some (.ok _, w2) => some (res, w2)
          | some (.error err, w2) => some (.error err, w2) := by
  simp only [tryFinallyL, ExceptT.run, ExceptT.mk, StateT.run, Bind.bind, StateT.bind,
    Option.bind, Pure.pure]
  cases body w with
  | none => rfl
  | some p1 =>
      rcases p1 with ⟨res, w1⟩
      dsimp only
      cases cleanup w1 with
      | none => rfl
      | some p2 => rcases p2 with ⟨res2, w2⟩; cases res2 <;> rfl

private theorem lm_tryCatch_run {X Y E D CI CF V α : Type} {o : LOps X Y E D CI CF V}
    (body : LM o α) (handler : LErr E → LM o α) (w : World X D CI CF) :
    StateT.run (ExceptT.run (tryCatchL o body handler)) w =
      match StateT.run (ExceptT.run body) w with
      | none => none
      | some (.ok a, w1) => some (.ok a, w1)
      | some (.error err, w1) => StateT.run (ExceptT.run (handler err)) w1 := by
  simp only [tryCatchL, ExceptT.run, ExceptT.mk, StateT.run, Bind.bind, StateT.bind,
    Option.bind, Pure.pure]
  cases body w with
  | none => rfl
  | some p1 => rcases p1 with ⟨res, w1⟩; cases res <;> rfl

private theorem lm_withLock_run {X Y E D CI CF V α : Type} {o : LOps X Y E D CI CF V}
    (body : LM o α) (w : World X D CI CF) :
    StateT.run (ExceptT.run (withLock o body)) w =
      match StateT.run (ExceptT.run body) { w with require_lock := w.require_lock + 1 } with
      | none => none
      | some (res, w1) => some (res, { w1 with require_lock := w1.require_lock - 1 }) := by
  simp only [withLock, ExceptT.run, ExceptT.mk, StateT.run, Bind.bind, StateT.bind,
    Option.bind, Pure.pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  cases body { w with require_lock := w.require_lock + 1 } <;> rfl

-- 1. models1-g9-toml-constructor-identity
theorem tomlConstructorIdentity_proven :
    Models1Group9.TOMLConstructor.SharesParserFreshEmptyDictionary := by
  intro X D CI CF allocation parser before
  cases allocation with
  | outOfMemory => exact ⟨rfl, rfl, rfl⟩
  | allocated =>
      dsimp only [JuliaLean.base.loading.Models1Group9.TOMLConstructor.construct,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get,
        EStateM.get, set, MonadStateOf.set, EStateM.set]
      refine ⟨rfl, rfl, rfl, rfl, List.length_append, ?_, Nat.le_refl _,
        JuliaLean.base.dict.dictEmpty _ _, ?_, rfl, rfl, rfl, wrap_u64_zero,
        fun _ => ⟨rfl, rfl, rfl⟩⟩
      · intro i hi
        exact List.getElem?_append_left hi
      · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl

-- 2. models1-g9-toml-constructor-fresh
theorem tomlConstructorFresh_proven :
    Models1Group9.TOMLConstructor.SeparateDictionaryIdentities := by
  intro X D CI CF firstAllocation secondAllocation parser before
  cases firstAllocation with
  | outOfMemory => exact ⟨rfl, rfl, rfl⟩
  | allocated =>
      dsimp only [JuliaLean.base.loading.Models1Group9.TOMLConstructor.construct,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get,
        EStateM.get, set, MonadStateOf.set, EStateM.set, throw, throwThe, MonadExceptOf.throw,
        EStateM.throw]
      refine ⟨rfl, ?_⟩
      cases secondAllocation with
      | outOfMemory => exact ⟨rfl, rfl, rfl⟩
      | allocated =>
          refine ⟨rfl, rfl, ?_⟩
          intro h
          have hid := congrArg JuliaLean.base.loading.Models1Group9.TOMLConstructor.DictRef.id h
          simp only [List.length_append, List.length_singleton] at hid
          omega

-- 3. models1-g9-cache-fetch-cleanup
private theorem getW_ext_bind {X Y E D CI CF V α : Type} (o : LOps X Y E D CI CF V)
    (f : Bool → LM o α) (w : World X D CI CF) :
    StateT.run (ExceptT.run ((do return (← getW o).loading_extension) >>= f)) w =
      StateT.run (ExceptT.run (f w.loading_extension)) w := rfl

private theorem modifyW_set_bind {X Y E D CI CF V α : Type} (o : LOps X Y E D CI CF V)
    (b : Bool) (next : LM o α) (w : World X D CI CF) :
    StateT.run (ExceptT.run ((modifyW o fun s => { s with loading_extension := b }) >>= fun _ => next)) w =
      StateT.run (ExceptT.run next) { w with loading_extension := b } := rfl

private theorem maybeFetchCache_probe_run {X Y E D CI CF V : Type} (o : LOps X Y E D CI CF V)
    (hookAvailable generating : Bool) (hookAction : LM o (JuliaLean.base.toml.parser.Val X))
    (loggerAction : LErr E → LM o Unit) (pkg : JuliaLean.base.pkgid.PkgId) (sourcePath : Bytes)
    (w : World X D CI CF) :
    (JuliaLean.base.loading.maybe_fetch_cache o
      (Models1Group9.cacheFetchProbe o hookAvailable generating hookAction loggerAction)
      pkg sourcePath).run.run w =
      if hookAvailable = false ∨ generating = true ∨ w.loading_extension = true then
        some (.ok false, w)
      else
        StateT.run (ExceptT.run (tryFinallyL o
          (tryCatchL o
            (do
              match ← hookAction with
              | .bool true => pure true
              | _ => pure false)
            (fun err => do
              loggerAction err
              pure false))
          (modifyW o fun w => { w with loading_extension := false })))
          { w with loading_extension := true } := by
  unfold JuliaLean.base.loading.maybe_fetch_cache
    Models1Group9.cacheFetchProbe
  dsimp only
  cases hookAvailable with
  | false => rfl
  | true =>
      cases generating with
      | true => rfl
      | false =>
          rw [lm_bind_run, lm_pure_run]
          simp only [↓reduceIte]
          rw [lm_bind_run, lm_pure_run]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [getW_ext_bind]
          cases hext : w.loading_extension with
          | true =>
              simp only [or_true, ↓reduceIte]
              rfl
          | false =>
              simp only [Bool.true_eq_false, false_or]
              exact modifyW_set_bind o true _ w

theorem cacheFetchCleanup_proven :
    Models1Group9.CacheFetchCleanup := by
  intro X Y E D CI CF V o hookAvailable generating hookAction loggerAction pkg sourcePath w
  dsimp only
  rw [maybeFetchCache_probe_run]
  by_cases hskip : hookAvailable = false ∨ generating = true ∨ w.loading_extension = true
  · simp only [hskip, ↓reduceIte]
  · simp only [hskip, ↓reduceIte]
    rw [lm_tryFinally_run, lm_tryCatch_run, lm_bind_run]
    cases StateT.run (ExceptT.run hookAction) { w with loading_extension := true } with
    | none => trivial
    | some p1 =>
        rcases p1 with ⟨res1, w1⟩
        cases res1 with
        | ok val =>
            cases val with
            | bool b => cases b <;> rfl
            | _ => rfl
        | error err =>
            dsimp only
            rw [lm_bind_run]
            cases StateT.run (ExceptT.run (loggerAction err)) w1 with
            | none => trivial
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                cases res2 <;> rfl

-- 4. models1-g9-cache-options-explicit
theorem cacheOptionsExplicit_proven :
    Models1Group9.CacheFlagOptions.ExplicitInput := by
  intro X Y E D CI CF V o cacheRuntime coverageRuntime options input overrides world
  refine ⟨JuliaLean.base.loading.Models1Group9.CacheFlagOptions.keywordBody
    input.flags (JuliaLean.base.loading.Models1Group9.CacheFlagOptions.eraseOverrides overrides),
    rfl, ?_⟩
  unfold Models1Group9.CacheFlagOptions.Fields
    JuliaLean.base.loading.Models1Group9.CacheFlagOptions.keywordBody
    JuliaLean.base.loading.Models1Group9.CacheFlagOptions.eraseOverrides
  dsimp only
  rw [eqSame_int_lit_i64_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [h]
  · intro v h; simp [h]
  · intro h; simp [h]
  · intro v h; simp [h]
  · intro h; simp [h]
  · intro v h; simp [h]
  · intro h; simp [h]
  · intro v h; simp [h]
  · intro h; simp [h]
  · intro v h; simp [h]
  · intro h; simp [h]
  · intro v h; simp [h]
  · intro h; simp [h]
  · intro hne
    simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · intro h; simp [h]
    · intro h; simp [h]
    · intro path h; simp [h]

-- 5. models1-g9-match-cache-coverage-checked-arguments
private theorem u8_min_eq : IntTy.u8.min = 0 := by decide
private theorem u8_max_eq : IntTy.u8.max = 255 := by decide

private theorem u8_range_iff (x : Int) :
    (IntTy.u8.min ≤ x ∧ x ≤ IntTy.u8.max) ↔ (0 ≤ x ∧ x ≤ 255) := by
  rw [u8_min_eq, u8_max_eq]

private theorem convert_u8_i64 (x : JInt .i64) :
    JuliaLean.base.int.convert .u8 x =
      if h : IntTy.u8.min ≤ x.val ∧ x.val ≤ IntTy.u8.max then .ok ⟨x.val, h⟩
      else .error (.inexactError "trunc") := rfl

theorem matchCacheCoverageCheckedArguments_proven :
    Models1Group9.Coverage.RejectsInvalidCoverageWithoutEffects := by
  intro X Y E D CI CF V o ops requested actual world _ _ hinv
  unfold JuliaLean.base.loading.Models1Group9.Coverage.matchCacheCoverage
  rw [convert_u8_i64 requested.coverage, convert_u8_i64 actual.coverage]
  by_cases hr : IntTy.u8.min ≤ requested.coverage.val ∧ requested.coverage.val ≤ IntTy.u8.max
  · have ha : ¬ (IntTy.u8.min ≤ actual.coverage.val ∧ actual.coverage.val ≤ IntTy.u8.max) := by
      rw [u8_range_iff] at hr ⊢
      rcases hinv with h | h | h | h <;> omega
    refine ⟨"trunc", ?_⟩
    simp only [hr, ha, ↓reduceDIte]
    rfl
  · refine ⟨"trunc", ?_⟩
    simp only [hr, ↓reduceDIte]
    rfl

-- 6. models1-g9-plain-coverage-accept-outcome
theorem plainCoverageAcceptOutcome_proven :
    Models1Group9.PlainCoverage.PreservesAcceptanceOutcome := by
  intro X Y E D CI CF V o ops action buildId world
  rfl

-- 7. models1-g9-plain-coverage-query-outcome
theorem plainCoverageQueryOutcome_proven :
    Models1Group9.PlainCoverage.PreservesQueryOutcome := by
  intro X Y E D CI CF V o ops action buildId world
  rfl

-- 8. models1-g9-sha-hash-equal
private theorem hashTuple_congr {α : Type} (ops1 ops2 : JuliaLean.base.tuple.Ops α)
    (h : ops1.hash = ops2.hash) (xs : List α) (seed : Nat) :
    JuliaLean.base.tuple.hashTuple ops1 xs seed =
      JuliaLean.base.tuple.hashTuple ops2 xs seed := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih =>
      simp only [JuliaLean.base.tuple.hashTuple, h, ih]

private theorem hashLongLoop_congr {α : Type} (ops1 ops2 : JuliaLean.base.tuple.Ops α)
    (h : ops1.hash = ops2.hash) (xs : List α) (k out : Nat) :
    JuliaLean.base.tuple.hashLongLoop ops1 xs k out =
      JuliaLean.base.tuple.hashLongLoop ops2 xs k out := by
  induction k generalizing out with
  | zero => rfl
  | succ k ih =>
      simp only [JuliaLean.base.tuple.hashLongLoop, h]
      cases xs[k]? with
      | none => rfl
      | some v => exact ih _

private theorem hashTupleMethod_congr {α : Type} (ops1 ops2 : JuliaLean.base.tuple.Ops α)
    (h : ops1.hash = ops2.hash) (xs : List α) (seed : Nat) :
    JuliaLean.base.tuple.hashTupleMethod ops1 xs seed =
      JuliaLean.base.tuple.hashTupleMethod ops2 xs seed := by
  unfold JuliaLean.base.tuple.hashTupleMethod JuliaLean.base.tuple.hashLong
  rw [hashLongLoop_congr ops1 ops2 h, hashTuple_congr ops1 ops2 h]

theorem shaHashEqual_proven :
    Models1Group9.SHAHash.EqualBytesEqualHash := by
  intro runtimeTypeHash byteOps1 byteOps2 pairOps1 pairOps2 kind left right seed hleft hright heq
  have hbytes : left.bytes = right.bytes := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < kind.width
    · exact heq i hi
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  unfold JuliaLean.base.loading.Models1Group9.SHAHash.hashDigest
  rw [hbytes]
  apply congrArg (fun n : Nat => JInt.wrap .u64 (Int.ofNat n))
  apply hashTupleMethod_congr
  funext elem s
  cases elem with
  | inl k => rfl
  | inr bs =>
      dsimp only [JuliaLean.base.loading.Models1Group9.SHAHash.pairBindings,
        JuliaLean.base.loading.Models1Group9.SHAHash.hashBytes]
      apply congrArg (fun w : JuliaLean.base.hashing.Word => w.val.toNat)
      apply congrArg (fun n : Nat => JInt.wrap .u64 (Int.ofNat n))
      apply hashTupleMethod_congr
      rfl


private theorem wrap_i64_one : wrapInt .i64 1 = 1 :=
  wrapInt_of_inRange .i64 1 (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])

private theorem wrap_i64_two : wrapInt .i64 2 = 2 :=
  wrapInt_of_inRange .i64 2 (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])

private theorem wrap_i64_three : wrapInt .i64 3 = 3 :=
  wrapInt_of_inRange .i64 3 (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])

private theorem wrap_i64_six : wrapInt .i64 6 = 6 :=
  wrapInt_of_inRange .i64 6 (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])

private theorem convert_i64_self (x : JInt .i64) :
    JuliaLean.base.int.convert .i64 x = .ok x := by
  unfold JuliaLean.base.int.convert JInt.convert
  exact dite_eq_left x.property

private theorem mod_two_zero_or_one (z : Int) : z % 2 = 0 ∨ z % 2 = 1 := by omega

private theorem boolFromReal_bit (x : JInt .i64) (hx : x.val = 0 ∨ x.val = 1) :
    JuliaLean.base.bool.boolFromReal
      (fun y n => pure (JuliaLean.base.int.eqSame y (JuliaLean.base.int.lit .i64 n))) x =
      .ok (decide (x.val = 1)) := by
  unfold JuliaLean.base.bool.boolFromReal JuliaLean.base.int.eqSame
  have h0 : (JuliaLean.base.int.lit .i64 0).val = 0 := wrap_i64_zero
  have h1 : (JuliaLean.base.int.lit .i64 1).val = 1 := wrap_i64_one
  dsimp only [Pure.pure, Except.pure]
  rw [JuliaLean.Proofs.base.int.eq_int_eq, JuliaLean.Proofs.base.int.eq_int_eq, h0, h1]
  rcases hx with hx | hx <;> simp [hx]

private theorem band_widen_u8_one_val (z : JInt .u8) :
    (JuliaLean.base.int.band (JuliaLean.base.int.widenTo .i64 z)
      (JuliaLean.base.int.lit .i64 1)).val = z.val % 2 := by
  have hz : 0 ≤ z.val ∧ z.val ≤ 255 := z.property
  have hw : (JuliaLean.base.int.widenTo .i64 z).val = z.val :=
    wrapInt_of_inRange .i64 z.val (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)
  have hpat_z : JuliaLean.Proofs.base.int.pattern (JuliaLean.base.int.widenTo .i64 z) = z.val.toNat := by
    rw [JuliaLean.Proofs.base.int.pattern_of_nonneg _ (by omega), hw]
  have hpat_1 : JuliaLean.Proofs.base.int.pattern (JuliaLean.base.int.lit .i64 1) = 1 := by decide
  rw [JuliaLean.Proofs.base.int.val_eq_wrap_pattern, JuliaLean.Proofs.base.int.pattern_band,
    hpat_z, hpat_1, Nat.and_one_is_mod]
  have hmod : ((z.val.toNat % 2 : Nat) : Int) = z.val % 2 := by omega
  rw [hmod]
  exact wrapInt_of_inRange .i64 (z.val % 2) (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

private theorem band_widen_u8_three_val (z : JInt .u8) :
    (JuliaLean.base.int.band (JuliaLean.base.int.widenTo .i64 z)
      (JuliaLean.base.int.lit .i64 3)).val = z.val % 4 := by
  have hz : 0 ≤ z.val ∧ z.val ≤ 255 := z.property
  have hw : (JuliaLean.base.int.widenTo .i64 z).val = z.val :=
    wrapInt_of_inRange .i64 z.val (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)
  have hpat_z : JuliaLean.Proofs.base.int.pattern (JuliaLean.base.int.widenTo .i64 z) = z.val.toNat := by
    rw [JuliaLean.Proofs.base.int.pattern_of_nonneg _ (by omega), hw]
  have hpat_3 : JuliaLean.Proofs.base.int.pattern (JuliaLean.base.int.lit .i64 3) = 3 := by decide
  rw [JuliaLean.Proofs.base.int.val_eq_wrap_pattern, JuliaLean.Proofs.base.int.pattern_band,
    hpat_z, hpat_3, Nat.and_two_pow_sub_one_eq_mod _ 2]
  have hmod : ((z.val.toNat % 2 ^ 2 : Nat) : Int) = z.val % 4 := by omega
  rw [hmod]
  exact wrapInt_of_inRange .i64 (z.val % 4) (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

private theorem shr_u8_val (flags : JInt .u8) (c : JInt .i64) (hc : 0 ≤ c.val) :
    (JuliaLean.base.int.shr_Int flags c).val = flags.val / ((2 ^ c.val.toNat : Nat) : Int) := by
  have h := (JuliaLean.Proofs.base.int.shiftIntCount_proven .u8 flags c).1
  rw [ite_eq_left hc] at h
  exact h


-- 1. loading-cacheflags-int-constructor
theorem intConstructorCorrect_proven :
    Models1Group9.Flags.IntConstructorCorrect := by
  intro flags
  unfold JuliaLean.base.loading.Models1Group9.Flags.fromInt
  rw [convert_u8_i64 flags]
  by_cases hr : IntTy.u8.min ≤ flags.val ∧ flags.val ≤ IntTy.u8.max
  · rw [dite_eq_left hr]
    have hbounds : 0 ≤ flags.val ∧ flags.val < 256 := by
      rw [u8_min_eq, u8_max_eq] at hr
      omega
    let byte : JInt .u8 := ⟨flags.val, hr⟩
    change (match JuliaLean.base.loading.Models1Group9.Flags.fromUInt8BitInteger byte
        (JuliaLean.base.int.lit .i64 0) with
      | .ok cf => _
      | .error (.inexactError _) => _
      | .error _ => False)
    unfold JuliaLean.base.loading.Models1Group9.Flags.fromUInt8BitInteger
    have hbit0 : (JuliaLean.base.int.band (JuliaLean.base.int.widenTo .i64 byte)
        (JuliaLean.base.int.lit .i64 1)).val = flags.val % 2 := band_widen_u8_one_val byte
    have hshr5 : (JuliaLean.base.int.shr_Int byte (JuliaLean.base.int.lit .i64 5)).val =
        flags.val / 32 := by
      have h5 : (JuliaLean.base.int.lit .i64 5).val = 5 := wrap_i64_five
      rw [shr_u8_val byte _ (by rw [h5]; omega), h5]
      rfl
    have hbit5 : (JuliaLean.base.int.band
        (JuliaLean.base.int.widenTo .i64
          (JuliaLean.base.int.shr_Int byte (JuliaLean.base.int.lit .i64 5)))
        (JuliaLean.base.int.lit .i64 1)).val = (flags.val / 32) % 2 := by
      rw [band_widen_u8_one_val, hshr5]
    rw [boolFromReal_bit _ (hbit0 ▸ mod_two_zero_or_one flags.val), boolFromReal_bit _ (hbit5 ▸ mod_two_zero_or_one (flags.val / 32)),
      convert_i64_self, convert_i64_self, convert_i64_self, convert_i64_self]
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, CacheFlags_fields]
    have hshr1 : (JuliaLean.base.int.shr_Int byte (JuliaLean.base.int.lit .i64 1)).val =
        flags.val / 2 := by
      have h1 : (JuliaLean.base.int.lit .i64 1).val = 1 := wrap_i64_one
      rw [shr_u8_val byte _ (by rw [h1]; omega), h1]
      rfl
    have hshr3 : (JuliaLean.base.int.shr_Int byte (JuliaLean.base.int.lit .i64 3)).val =
        flags.val / 8 := by
      have h3 : (JuliaLean.base.int.lit .i64 3).val = 3 := wrap_i64_three
      rw [shr_u8_val byte _ (by rw [h3]; omega), h3]
      rfl
    have hshr6 : (JuliaLean.base.int.shr_Int byte (JuliaLean.base.int.lit .i64 6)).val =
        flags.val / 64 := by
      have h6 : (JuliaLean.base.int.lit .i64 6).val = 6 := wrap_i64_six
      rw [shr_u8_val byte _ (by rw [h6]; omega), h6]
      rfl
    refine ⟨hbounds.1, hbounds.2, ?_, ?_, ?_, ?_, ?_, wrap_i64_zero, rfl⟩
    · rw [hbit0]
    · rw [band_widen_u8_three_val, hshr1]
    · rw [band_widen_u8_three_val, hshr3]
    · rw [hbit5]
    · rw [band_widen_u8_three_val, hshr6]
  · rw [dite_eq_right hr]
    dsimp only [Bind.bind, Except.bind]
    rw [u8_min_eq, u8_max_eq] at hr
    omega


namespace Models1Group9
open JuliaLean.base.loading.Models1Group9

private theorem shaScalarEq (ops : JuliaLean.base.tuple.Ops UInt8) (a b : UInt8) :
    (shaTupleBindings ops).eq a b = some (a == b) := by
  change some ((JuliaLean.ChatGPT.Batch4.Group11.shaTupleBindings ops).isequal a b) = _
  rw [JuliaLean.ChatGPT.Batch4.Group11.shaTupleEqual]

private theorem shaTupleCodes (ops : JuliaLean.base.tuple.Ops UInt8) (a b : List UInt8)
    (lengths : a.length = b.length) :
    JuliaLean.Proofs.base.tuple.eqCode (List.zipWith (shaTupleBindings ops).eq a b) false =
      some (decide (a = b)) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp at lengths
  | cons x xs ih =>
    cases b with
    | nil => simp at lengths
    | cons y ys =>
      have tails : xs.length = ys.length := Nat.succ.inj lengths
      rw [List.zipWith_cons_cons, shaScalarEq]
      by_cases same : x = y
      · subst y
        simp only [BEq.rfl]
        rw [JuliaLean.Proofs.base.tuple.eqCodeTrue, ih ys tails]
        simp
      · have different : (x == y) = false := by simp [same]
        rw [different, JuliaLean.Proofs.base.tuple.eqCodeFalse]
        simp [same]

private theorem shaValuePlace (bytes : List UInt8) :
    shaValue bytes = JuliaLean.ChatGPT.Batch4.Group11.shaPlaceValue bytes := by
  induction bytes with
  | nil => rfl
  | cons x xs ih => simp only [shaValue, JuliaLean.ChatGPT.Batch4.Group11.shaPlaceValue, ih]

theorem shaEquality_proven : ShaEquality := by
  intro ops n a b width lengthA lengthB
  have lengths : a.bytes.length = b.bytes.length := lengthA.trans lengthB.symm
  unfold shaEqual
  rw [JuliaLean.Proofs.base.tuple.eqTupleMethodEq]
  unfold JuliaLean.Proofs.base.tuple.eqSpec
  rw [if_neg (by omega), shaTupleCodes ops a.bytes b.bytes lengths]
  have values : shaValue a.bytes = shaValue b.bytes ↔ a.bytes = b.bytes := by
    rw [shaValuePlace, shaValuePlace]
    exact ⟨JuliaLean.ChatGPT.Batch4.Group11.shaPlaceInjective a.bytes b.bytes lengths,
      fun equality => congrArg _ equality⟩
  simp only [values]

end Models1Group9

namespace Models1Group9.PlainCoverage


private theorem lowWordBit (number : Int) (index : Nat) (within : index < 64) :
    ((number % (2 : Int)^64) / (2 : Int)^index) % 2 =
      (number / (2 : Int)^index) % 2 := by
  have factor : (2 : Int)^64 = (2 : Int)^index * (2 * (2 : Int)^(63-index)) := by
    have exponent : 64 = index + (1 + (63-index)) := by omega
    conv => lhs; rw [exponent]
    rw [Int.pow_add, Int.pow_add]
    rfl
  have nonzero : (2 : Int)^index ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  have product : (2 : Int)^64 * (number / (2 : Int)^64) =
      (2 : Int)^index * (2 * ((2 : Int)^(63-index) * (number / (2 : Int)^64))) := by
    rw [factor]
    simp only [Int.mul_assoc]
  calc
    ((number % (2 : Int)^64) / (2 : Int)^index) % 2 =
        (((number % (2 : Int)^64) / (2 : Int)^index) +
          2 * ((2 : Int)^(63-index) * (number / (2 : Int)^64))) % 2 := by simp
    _ = ((number % (2 : Int)^64 + (2 : Int)^64 * (number / (2 : Int)^64)) /
        (2 : Int)^index) % 2 := by
      rw [product, Int.add_mul_ediv_left _ _ nonzero]
    _ = (number / (2 : Int)^index) % 2 := by rw [Int.emod_add_mul_ediv]

private theorem nativeHighValue (value : JInt .u128) :
    (JuliaLean.base.int.rem_BitInteger_Type .u64
      (JuliaLean.base.int.shr_Int value (i64 64))).val = value.val / (2 : Int)^64 := by
  rw [JuliaLean.Proofs.base.int.rem_BitInteger_Type_val]
  have shifted := (JuliaLean.Proofs.base.int.shiftIntCount_proven .u128 value (i64 64)).1
  have literal : (i64 64).val = 64 := by decide
  rw [literal] at shifted
  simp only [show (0 : Int) ≤ 64 by decide, ite_true] at shifted
  rw [shifted]
  apply wrapInt_of_inRange
  have range := value.property
  change 0 ≤ value.val ∧ value.val ≤ 340282366920938463463374607431768211455 at range
  change 0 ≤ value.val / 18446744073709551616 ∧
    value.val / 18446744073709551616 ≤ 18446744073709551615
  omega

private theorem nativeLowValue (value : JInt .u128) :
    (JuliaLean.base.int.rem_BitInteger_Type .u64 value).val = value.val % (2 : Int)^64 := by
  rw [JuliaLean.Proofs.base.int.rem_BitInteger_Type_val]
  rfl

theorem passesWordsPositionally_proven : PassesWordsPositionally := by
  intro X Y D CI CF V o ops buildId world
  refine ⟨JuliaLean.base.int.rem_BitInteger_Type .u64
      (JuliaLean.base.int.shr_Int buildId (i64 64)),
    JuliaLean.base.int.rem_BitInteger_Type .u64 buildId, ?_, rfl, rfl⟩
  intro index
  rw [nativeHighValue, nativeLowValue]
  constructor
  · rw [Int.ediv_ediv_of_nonneg (by decide), Int.pow_add]
    rw [Int.mul_comm ((2 : Int)^index.val) ((2 : Int)^64)]
  · exact lowWordBit buildId.val index.val index.isLt
end Models1Group9.PlainCoverage


def entriesModels1Group9 : List Entry := [
  {
    id := "loading-sha-equality"
    juliaFile := "base/loading.jl"
    juliaFns := ["==(::SHA1, ::SHA1)", "==(::SHA256, ::SHA256)"]
    statement := "Equality reaches the installed short/long tuple and UInt8 methods and returns a Boolean equal to equality of the complete positional digest values, for every valid SHA1 and SHA256."
    source := "base/loading.jl:114-143; base/operators.jl:109-118; NTuple representation invariant"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.ShaEquality, thm := some ``Models1Group9.shaEquality_proven },
  {
    id := "loading-slug-output"
    juliaFile := "base/loading.jl"
    juliaFns := ["slug(x::UInt32, p::Int)"]
    statement := "For every UInt32, Int64 precision, raw allocation outcome and initial storage content, successful required allocations produce exactly max(p,0) least-significant-first base62 digits; failure of any required String, Memory or IOBuffer allocation returns OutOfMemoryError. Nonpositive precision still requires the mutable IOBuffer allocation."
    source := "base/loading.jl:185-198; base/iobuffer.jl:96-107,246-270; base/strings/string.jl:184-185,195"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.Slug.OutputInvariant, thm := none
    notes := "Concrete installed arithmetic, String indexing, range and Char writes; allocation-aware local IOBuffer constructor binds only existing raw GC boundaries. Exact-capacity writes need no resize or final String copy. All outcomes and initial bytes are quantified; no runtime correctness law or success-domain restriction." },
  {
    id := "loading-cache-fetch-cleanup"
    juliaFile := "base/loading.jl"
    juliaFns := ["maybe_fetch_cache(::PkgId, ::String)"]
    statement := "Unavailable, output-generation and reentrant hook cases return false without effects; every entered finite call clears the TLS guard, including hook and logger exceptions."
    source := "base/loading.jl:1688-1735; documented safety guards and finally invariant"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CacheFetchCleanup, thm := some ``JuliaLean.Proofs.base.loading.cacheFetchCleanup_proven
    notes := "The concrete protocol observer uses one existing World Boolean as an isolated TLS bit, not as an installed task-storage implementation; hook and logger effects remain arbitrary." },
  {
    id := "loading-cacheflags-int-constructor"
    juliaFile := "base/loading.jl"
    juliaFns := ["CacheFlags(::Int)"]
    statement := "Every Int input in 0:255 decodes into its positional cache-flag fields with coverage zero and no coverage path; all other Int inputs raise InexactError."
    source := "base/loading.jl:1971-1979; independent constructor digit and checked-conversion invariant"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.Flags.IntConstructorCorrect, thm := some ``JuliaLean.Proofs.base.loading.intConstructorCorrect_proven
    notes := "All native Int64 inputs; the broader coverage::Integer overload remains partial for Bool, BigInt and user-defined Integer subtypes." },
  {
    id := "loading-cacheflags-byte-encoding"
    juliaFile := "base/loading.jl"
    juliaFns := ["_cacheflag_to_uint8(::CacheFlags)"]
    statement := "Across every constructible CacheFlags value, byte encoding is the positional union of the 64-bit source field bits when it fits UInt8, and otherwise raises InexactError."
    source := "base/loading.jl:2012-2020; doc/src/manual/integers-and-floating-point-numbers.md:231-249; independent bit-layout invariant"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.Flags.ByteEncodingCorrect, thm := none
    notes := "Negative fields, shifted-out high bits and overlaps are included. Only the final return performs checked UInt8 conversion." },
  {
    id := "loading-sha-print"
    juliaFile := "base/loading.jl"
    juliaFns := ["print(::IO, ::SHA1)", "print(::IO, ::SHA256)"]
    statement := "SHA printing requests exactly two lowercase hexadecimal digits per stored byte; every primitive failure schedule preserves the requested prefix, propagates the error and attempts all applicable unlocks, including IOContext forwarding; a later cleanup error takes precedence."
    source := "base/loading.jl:114-138; base/strings/util.jl:1286-1291,1329-1334; base/strings/io.jl:42-54"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.SHAIO.PrintCorrect, thm := none
    notes := "Concrete fault-injecting observation of the existing arbitrary-IO primitive boundary. Requested bytes on a failed write are not claimed to have been committed by the external stream." },
  {
    id := "loading-sha-show"
    juliaFile := "base/loading.jl"
    juliaFns := ["show(::IO, ::SHA1)", "show(::IO, ::SHA256)"]
    statement := "For every SHA1/SHA256 value, raw String-allocation outcome, initial storage content and IO primitive failure schedule, prefix allocation failure returns OutOfMemoryError before any IO event; successful allocation requests constructor syntax with lowercase hexadecimal digits, retaining the requested prefix and all applicable unlock attempts when IO fails, with later cleanup errors taking precedence."
    source := "base/loading.jl:114-139; base/strings/basic.jl:257-263; base/strings/substring.jl:233-283; base/strings/string.jl:184-185; base/strings/io.jl:42-54"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.SHAIO.ShowCorrect, thm := none
    notes := "Concrete installed String concatenation, allocation, pointer, unsafe-copy and StandardC memmove bodies replace the constant-prefix shortcut. The source performs a 6/8-byte String allocation before entering print. All raw outcomes and arbitrary fresh bytes are quantified; no allocation-success or IO-correctness assumption. Plain streams and IOContexts are included; requested bytes do not claim committed external-stream output. PrintCorrect and printDigest retain their prior contracts." },
  {
    id := "loading-match-cache-coverage-checked-arguments"
    juliaFile := "base/loading.jl"
    juliaFns := ["match_cache_coverage(::CacheFlags, ::CacheFlags)"]
    statement := "A requested or actual coverage value outside UInt8 raises InexactError with unchanged loading state, independently of every possible runtime matcher action."
    source := "base/loading.jl:2044-2046; checked argument conversion invariant"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.Coverage.RejectsInvalidCoverageWithoutEffects, thm := some ``JuliaLean.Proofs.base.loading.matchCacheCoverageCheckedArguments_proven
    notes := "Concrete installed checked integer conversions run before the existing jl_match_cache_coverage boundary. Runtime exceptions/state/divergence remain in LM; conversion errors use outer ExceptT JlError. No C matching semantics or runtime correctness law is assumed." },
  {
    id := "loading-sha-string"
    juliaFile := "base/loading.jl"
    juliaFns := ["string(::SHA1)", "string(::SHA256)"]
    statement := "A SHA1 or SHA256 String contains exactly two lowercase hexadecimal digits per digest byte in order, independently of uninitialized allocation contents; allocation failure at the required 40/64-byte size propagates as OutOfMemoryError."
    source := "base/loading.jl:114-137; base/strings/util.jl:1286-1291,1316-1327; base/strings/string.jl:184-185"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.SHAString.StringCorrect, thm := none
    notes := "Uses installed bytes2hex, stringN, checked UInt64 conversion, jlAllocString, tuple/enumerate and typed pointer stores. Only the existing allocation-outcome boundary and arbitrary fresh-memory contents are inputs; no encoder callback or correctness law. The existing JString size invariant is automatic at digest widths20/32." },
  {
    id := "loading-sha-hash-seed"
    juliaFile := "base/loading.jl"
    juliaFns := ["hash(::SHA1, ::UInt)", "hash(::SHA256, ::UInt)"]
    statement := "For each fixed SHA1/SHA256 digest and every runtime type-hash result, the UInt64 seed is mixed injectively: output hashes are equal exactly when the seeds are equal."
    source := "base/loading.jl:114-142; base/tuple.jl:602-610; base/hashing.jl:44-45,55-63,75-77"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.SHAHash.SeedInjective, thm := none
    notes := "Independent seed-mixing invariant; does not claim collision freedom between different digests. Only the existing jl_type_hash primitive remains an input." },
  {
    id := "loading-sha-hash-equal"
    juliaFile := "base/loading.jl"
    juliaFns := ["hash(::SHA1, ::UInt)", "hash(::SHA256, ::UInt)"]
    statement := "Generated SHA digests with equal bytes hash equally for every UInt64 seed and runtime type-hash result, independently of unused tuple-interface fields."
    source := "base/loading.jl:114-143; base/hashing.jl:11-20"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.SHAHash.EqualBytesEqualHash, thm := some ``JuliaLean.Proofs.base.loading.shaHashEqual_proven
    notes := "All generated digest bytes and seeds; actual NTuple width is the sole representation premise. Actual tuple and integer hash dispatches are concretely bound." },
  {
    id := "loading-uuid5-version-variant"
    juliaFile := "base/loading.jl"
    juliaFns := ["uuid5(namespace::UUID, key::String)"]
    statement := "For every UUID namespace and every constructible String, including malformed UTF-8, fake uuid5 returns successfully with version nibble 5 and RFC variant bits 10."
    source := "base/loading.jl:147-160"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.Uuid5.VersionVariant, thm := none
    notes := "Concrete installed String/byte and UInt64/tuple hashing is bound; no supplied hash correctness law. The sole unused tuple-interface fields are quantified freely. This is the source's fake UUID5 format invariant, not a claim of SHA-1 UUID5 compatibility." },
  {
    id := "loading-crc-slug-format"
    juliaFile := "base/loading.jl"
    juliaFns := ["package_slug(uuid::UUID, p::Int=5)", "version_slug(uuid::UUID, sha1::SHA1, p::Int=5)"]
    statement := "For every raw CRC32C runtime, reference/buffer allocation outcome and Int precision, package/version slugs have exactly max(p,0) ASCII letters/digits when their required allocations succeed, and return OutOfMemoryError otherwise. RefValue and IOBuffer headers remain required at nonpositive precision."
    source := "base/loading.jl:187-209; base/refvalue.jl:5-10; base/refpointer.jl:113; base/uuid.jl:39; base/util.jl:515-518,542-543"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CRCSlugs.Formatting, thm := none
    notes := "Concrete allocation-aware slug body. UUID and tuple CRC composition uses the existing jl_crc32c C boundary with UInt32 seeds and Csize_t counts. RefValue new outcomes precede the corresponding raw CRC calls. Full-domain property quantifies all outcomes and makes no CRC or constructor correctness assumption." },
  {
    id := "loading-toml-constructor-identity"
    juliaFile := "base/loading.jl"
    juliaFns := ["TOMLCache(p::TOML.Parser)"]
    statement := "For every raw Dict allocation outcome, successful TOMLCache construction retains the parser reference, creates a fresh empty dictionary and preserves old objects; OutOfMemoryError preserves the entire old heap."
    source := "base/loading.jl:290-294; base/dict.jl:77-82"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.TOMLConstructor.SharesParserFreshEmptyDictionary, thm := some ``JuliaLean.Proofs.base.loading.tomlConstructorIdentity_proven
    notes := "Constructor-only local object heap; installed empty Dict fields and raw mutable-object allocation outcome. Zero-length memories are shared. No parser copy or arbitrary callee implementation is supplied; existing callers are unchanged." },
  {
    id := "loading-toml-constructor-fresh"
    juliaFile := "base/loading.jl"
    juliaFns := ["TOMLCache(p::TOML.Parser)"]
    statement := "For all paired raw allocation outcomes, two successful TOMLCache constructions share the parser and receive distinct mutable dictionaries; any failed call preserves its input heap."
    source := "base/loading.jl:290-294"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.TOMLConstructor.SeparateDictionaryIdentities, thm := some ``JuliaLean.Proofs.base.loading.tomlConstructorFresh_proven
    notes := "Independent identity observation; equality of empty contents cannot satisfy this property if a global dictionary object is reused." },
  {
    id := "loading-current-coverage-memory"
    juliaFile := "base/loading.jl"
    juliaFns := ["current_coverage_path()"]
    statement := "A single typed options-memory snapshot determines path coverage: disabled flags return nothing, a selected null pointer raises ArgumentError, and a selected readable C string is copied through its first NUL or reports allocation failure; invalid C memory remains undefined."
    source := "base/loading.jl:2004-2008; base/options.jl:4-85; base/strings/string.jl:176-179"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageMemory.CompleteOutcome, thm := none
    notes := "All physical options bytes are quantified on the supplied 64-bit little-endian ABI; actual Int8 fields and Ptr{UInt8} are concretely decoded by the supplied pointer model. Only existing C strlen/allocation primitives remain inputs. The expected first-NUL copy and address arithmetic are independent of the model body." },
  {
    id := "loading-string-vector-membership"
    juliaFile := "base/loading.jl"
    juliaFns := ["ext_may_load_weakdep(exts::Vector{String}, name::String)"]
    statement := "Every constructible String vector terminates with true for a match before any unassigned cell, false for all assigned unequal cells, or UndefRefError when a gap precedes the first match."
    source := "base/loading.jl:783; base/operators.jl:1455; base/anyall.jl:120-132"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.StringVectorMembership.MembershipOutcome, thm := none
    notes := "Concrete installed membership/Fix2/any and native Array iteration with shared mutable-memory reads. All unassigned cells, shifted aliases, malformed UTF-8 and embedded NUL are included. Only actual machine-sized vector/String representation invariants are required; independent positional prefix predicates supply the expected outcomes." },
  {
    id := "loading-string-vector-dependency"
    juliaFile := "base/loading.jl"
    juliaFns := ["dep_stanza_get(stanza::Vector{String}, name::String)"]
    statement := "A matching String before any unassigned cell returns the exact requested name with no UUID; complete absence returns nothing, while an earlier unassigned reference raises UndefRefError."
    source := "base/loading.jl:1142-1145; base/pkgid.jl:8,10"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.StringVectorMembership.DependencyOutcome, thm := none
    notes := "Concrete installed membership/Fix2/any and native Array iteration with shared mutable-memory reads. All unassigned cells, shifted aliases, malformed UTF-8 and embedded NUL are included. Only actual machine-sized vector/String representation invariants are required; independent positional prefix predicates supply the expected outcomes." },
  {
    id := "loading-cache-options-explicit"
    juliaFile := "base/loading.jl"
    juliaFns := ["CacheFlags(cf::CacheFlags; use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage, coverage_path)"]
    statement := "An explicit complete CacheFlags value skips default runtime calls and preserves every field unless its keyword is supplied; zero final coverage clears the path, for all Bool/Int64/String/nothing keyword combinations."
    source := "base/loading.jl:1980-1999"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CacheFlagOptions.ExplicitInput, thm := some ``JuliaLean.Proofs.base.loading.cacheOptionsExplicit_proven
    notes := "Only actual String representation bounds constrain explicit inputs; all other fields and keywords retain their full source domains. Fields is an independent implication-based observation of keyword behavior." },
  {
    id := "loading-cache-options-default"
    juliaFile := "base/loading.jl"
    juliaFns := ["CacheFlags(; use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage, coverage_path)"]
    statement := "Default construction preserves cache-flags then image-coverage C action order/state/errors, obtains the concrete options C-string outcome, decodes the runtime byte, applies the inner path-clearing constructor and only then applies outer keywords."
    source := "base/loading.jl:1980-2001; base/options.jl:85; base/strings/string.jl:176-179"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CacheFlagOptions.DefaultInput, thm := none
    notes := "Flags.fromUInt8BitInteger binds the required UInt8 specialization; the complete Integer overload at source2000 remains outside this helper. The expected byte fields use independent arithmetic, and path outcomes use physical first-NUL relations. No whole constructor or current_coverage_path callback is assumed." },
  {
    id := "loading-current-coverage-request"
    juliaFile := "base/loading.jl"
    juliaFns := ["is_current_coverage_request(requested::CacheFlags)"]
    statement := "The image coverage runtime is queried exactly after a present requested path matches the selected first-NUL options path; all earlier false/error/undefined-memory outcomes leave state unchanged, and a matching path preserves the runtime action while comparing its UInt8 result with every Int64 coverage request."
    source := "base/loading.jl:2062-2064; base/options.jl:85; base/strings/string.jl:176-179,238"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CurrentCoverageRequest.CompleteOutcome, thm := none
    notes := "The complete CacheFlags record carries only its actual String-field size invariant. current_coverage_path is concretely bound to section076; String identity is byte equality at its existing primitive boundary, with no invented oversized-result error. Expected path matching is positional, and the expected final numeric comparison is mathematical integer equality." },
  {
    id := "loading-coverage-options-fresh-vector"
    juliaFile := "base/loading.jl"
    juliaFns := ["coverage_cache_options"]
    statement := "Every successful call returns the specified command-line bytes in a fresh mutable String vector and preserves all old array headers/memories; failures preserve every old object."
    source := "base/loading.jl:2036-2041; base/array.jl:159-166"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CoverageOptions.FreshCommandVector, thm := none
    notes := "Full native CacheFlags domain with only the installed String input bound. Actual concat/copy/allocation and shared-array writes are bound; command bytes have an independent positional specification. Raw output strings have no artificial JStr length guard." },
  {
    id := "loading-coverage-options-allocation-order"
    juliaFile := "base/loading.jl"
    juliaFns := ["coverage_cache_options"]
    statement := "Across every raw allocation plan, calls reach exactly the required String, Memory and Array-header sites in source order, stopping with OutOfMemoryError at the first refused site and retaining preceding allocation effects."
    source := "base/loading.jl:2036-2041; base/boot.jl:821-824; base/strings/substring.jl:256-283"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CoverageOptions.AllocationOrderAndErrors, thm := none
    notes := "Disabled coverage still allocates its mutable vector. Absent paths skip only scope concatenation. Every native integer flag value and arbitrary initial String storage are included; no success premise or supplied callee law is used." },
  {
    id := "loading-coverage-options-distinct-identities"
    juliaFile := "base/loading.jl"
    juliaFns := ["coverage_cache_options"]
    statement := "Two successful coverage option calls yield distinct mutable vector identities, even when their contents agree, and constructing the second preserves the first result's live cells."
    source := "base/loading.jl:2036-2041; base/array.jl:159-166"
    status := .todo
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.CoverageOptions.SeparateResultIdentities, thm := none
    notes := "Both runs quantify all raw outcomes; failures are covered separately by the full allocation-order contract. Logical heap handles denote object identity, not a Julia integer length." },
  {
    id := "loading-plain-coverage-native-words"
    juliaFile := "base/loading.jl"
    juliaFns := ["accept_plain_coverage_cache", "plain_coverage_cache_accepted"]
    statement := "For every UInt128 build ID, both wrappers pass bits64-127 as the first UInt64 and bits0-63 as the second, preserving an observing boundary error and initial state."
    source := "base/loading.jl:2067-2070; base/int.jl:608-612,618-634"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.PlainCoverage.PassesWordsPositionally, thm := some ``Models1Group9.PlainCoverage.passesWordsPositionally_proven
    notes := "An independent positional bit relation specifies both words. The existing C boundary is instrumented only in the property to report actual arguments; no correctness law or restricted domain is assumed." },
  {
    id := "loading-plain-coverage-accept-outcome"
    juliaFile := "base/loading.jl"
    juliaFns := ["accept_plain_coverage_cache"]
    statement := "Native argument preparation preserves the acceptance C boundary complete stateful outcome, including exact runtime errors and divergence, for every UInt128 input."
    source := "base/loading.jl:2067-2068"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.PlainCoverage.PreservesAcceptanceOutcome, thm := some ``JuliaLean.Proofs.base.loading.plainCoverageAcceptOutcome_proven
    notes := "Quantifies arbitrary stateful actions at the existing C boundary. This is an effect-preservation invariant, not a model of the accepted-image set or a same-area value-model comparison." },
  {
    id := "loading-plain-coverage-query-outcome"
    juliaFile := "base/loading.jl"
    juliaFns := ["plain_coverage_cache_accepted"]
    statement := "Native argument preparation preserves either Boolean query result, exact runtime errors, final world and divergence for every UInt128 input."
    source := "base/loading.jl:2069-2070"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group9.PlainCoverage.PreservesQueryOutcome, thm := some ``JuliaLean.Proofs.base.loading.plainCoverageQueryOutcome_proven
    notes := "The existing normalized Cint Boolean boundary remains explicit. Arbitrary stateful outcomes are included without success or C-callee correctness premises." }
]

end JuliaLean.Proofs.base.loading


-- UNCHECKED group-10 additions: source review only; no successful Lean elaboration.

namespace JuliaLean.Proofs.base.loading.Models1Group10

open JuliaLean
open JuliaLean.base.loading

/-- The public declaration accepts an ordinary evaluation, and rejects a
non-precompilable file during either incremental or system-image generation.
The C query is instantiated with its raw Cint observation, over every Cint
value and both Bool arguments. The options action is arbitrary, so a model
that wrongly filters by incremental mode fails this statement. This binds
an existing runtime observation; it assumes no callee-correctness law.
Julia documentation: base/loading.jl:2795-2808;
base/runtime_internals.jl:1829-1847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrecompileAdmission : Prop :=
  ∀ (X Y D CI CF V : Type)
      (o : LOps X Y JuliaLean.base.io.Error D CI CF V)
      (world : World X D CI CF) (outputFlag : JInt .i32)
      (optionsIncremental : JuliaLean.base.io.M (World X D CI CF) Bool)
      (permitted : Bool),
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.__precompile__ o
        (pure outputFlag) optionsIncremental permitted)) world
    (observed = some (.ok (), world) ↔
      permitted = true ∨ outputFlag.val = 0) ∧
    (observed = some (.error .precompilableError, world) ↔
      permitted = false ∧ outputFlag.val ≠ 0)

/-- Declaring a file precompilable is harmless, even for a runtime observation
that would otherwise mutate state, fail, or diverge. Every world and runtime
action is quantified; there is no successful-run premise.
Julia source/documentation: base/loading.jl:2797-2808
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrecompilePermittedDoesNotObserveRuntime : Prop :=
  ∀ (X Y D CI CF V : Type)
      (o : LOps X Y JuliaLean.base.io.Error D CI CF V)
      (world : World X D CI CF)
      (outputQuery : JuliaLean.base.io.M (World X D CI CF) (JInt .i32))
      (optionsIncremental : JuliaLean.base.io.M (World X D CI CF) Bool),
    StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.__precompile__ o
        outputQuery optionsIncremental true)) world = some (.ok (), world)

/-- Refusing precompilation does not erase an exception or post-error state
from the established C/runtime observation boundary, and does not turn a
nonterminating observation into a terminating result. This is an effect
invariant over all supplied primitive behaviors, not a law assumed of them.
Julia source: base/loading.jl:2803-2808
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrecompileRuntimeFailurePreserved : Prop :=
  ∀ (X Y D CI CF V : Type)
      (o : LOps X Y JuliaLean.base.io.Error D CI CF V)
      (world : World X D CI CF)
      (outputQuery : JuliaLean.base.io.M (World X D CI CF) (JInt .i32))
      (optionsIncremental : JuliaLean.base.io.M (World X D CI CF) Bool),
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.__precompile__ o
        outputQuery optionsIncremental false)) world
    match outputQuery world with
    | none => observed = none
    | some (.error (error, nextWorld)) =>
        observed = some (.error (.ext error), nextWorld)
    | some (.ok (flag, nextWorld)) =>
        (observed = some (.ok (), nextWorld) ↔ flag.val = 0) ∧
        (observed = some (.error .precompilableError, nextWorld) ↔ flag.val ≠ 0)

end JuliaLean.Proofs.base.loading.Models1Group10

namespace JuliaLean.Proofs.base.loading.Models1Group10

open JuliaLean
open JuliaLean.base.loading

/-- Whenever the actual C hint and wrapper both return normally, the wrapper's
Bool records exactly whether that observed signed Int32 status is nonzero.
All original operation fields and states are retained, including mutations in
preceding operations. The complete represented signature and runtime-action
domains are quantified; there are no effect-free fixture substitutions.
The complementary effect/short-circuit contracts cover errors, divergence,
and whether normal termination is required. No compiler-success guarantee
or callee-correctness law is assumed.
Julia source/invariant: base/loading.jl:5225-5231;
Julia documentation: base/loading.jl:5215-5222
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrecompileHintFlagResult : Prop :=
  ∀ (X Y E D CI CF V Function FunctionType ArgTypes Signature
      Method StaticParams MethodInstance : Type)
      (o : LOps X Y E D CI CF V)
      (ops : CompilerMethodOps o Function FunctionType ArgTypes Signature Method StaticParams MethodInstance)
      (argtype : Signature) (world : World X D CI CF),
    let hintResult := StateT.run (ExceptT.run (ops.compileHint argtype)) world
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.precompile_type o ops argtype)) world
    match hintResult, observed with
    | some (.ok rawFlag, _), some (.ok result, _) =>
        (result = true ↔ rawFlag.val ≠ 0) ∧
        (result = false ↔ rawFlag.val = 0)
    | _, _ => True

/-- A successful C hint returns true in the post-hint world without observing
an arbitrary warning-ref or logging action. These actions may mutate state,
throw, or diverge. The premise is the actual result of the existing runtime
boundary, not a supplied correctness law; every signature, state and action
is quantified. This invariant detects eager lifting of a monadic RHS under &&.
Julia source/invariant: base/loading.jl:5226-5230
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrecompileHintSuccessSkipsWarnings : Prop :=
  ∀ (X Y E D CI CF V Function FunctionType ArgTypes Signature
      Method StaticParams MethodInstance : Type)
      (o : LOps X Y E D CI CF V)
      (ops : CompilerMethodOps o Function FunctionType ArgTypes Signature Method StaticParams MethodInstance)
      (argtype : Signature) (world : World X D CI CF),
    match StateT.run (ExceptT.run (ops.compileHint argtype)) world with
    | some (.ok rawFlag, nextWorld) =>
        rawFlag.val ≠ 0 →
          StateT.run (ExceptT.run
            (JuliaLean.base.loading.Models1Group10.precompile_type o ops argtype)) world =
            some (.ok true, nextWorld)
    | _ => True

/-- After an actual zero-status hint, the warning-ref read is observed at the
real post-hint world. If it returns false, the wrapper must retain that
read's post-state, return false, and skip an arbitrary logger. All original
operations remain in place, so resetting state after the hint is detectable.
Mutating, throwing and nonterminating loggers remain in the quantified domain.
Julia source/invariant: base/loading.jl:5227-5230
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrecompileHintDisabledWarningsSkipLogger : Prop :=
  ∀ (X Y E D CI CF V Function FunctionType ArgTypes Signature
      Method StaticParams MethodInstance : Type)
      (o : LOps X Y E D CI CF V)
      (ops : CompilerMethodOps o Function FunctionType ArgTypes Signature Method StaticParams MethodInstance)
      (argtype : Signature) (world : World X D CI CF),
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.precompile_type o ops argtype)) world
    match StateT.run (ExceptT.run (ops.compileHint argtype)) world with
    | some (.ok rawFlag, hintWorld) =>
        rawFlag.val = 0 →
          match StateT.run (ExceptT.run ops.warningsEnabled) hintWorld with
          | some (.ok false, warningWorld) => observed = some (.ok false, warningWorld)
          | _ => True
    | _ => True

/-- Observation relation used only to describe preservation of a failing
primitive effect. Error payloads and post-error states must be unchanged;
nontermination must not be replaced by a return. Successful outcomes make no
claim here; all source branches with successful primitive outcomes are covered
by the complementary contracts and the reached-diagnostic clause below. -/
def FailedHintEffectPreserved {E W A : Type}
    (effect : Option (Except (LErr E) A × W))
    (observed : Option (Except (LErr E) Bool × W)) : Prop :=
  match effect with
  | none => observed = none
  | some (.error error, nextWorld) => observed = some (.error error, nextWorld)
  | some (.ok _, _) => True

/-- Actual failures at the C hint, warning-ref read and logger retain their
exception payload and post-error world, and divergence remains divergence.
Every reached operation is observed in the state produced by the actual
preceding operation: warning reads use the post-hint state and diagnostics
use the post-read state. A successful enabled diagnostic must also retain
its final world and return false. This covers mutation sequencing in both
successful and failing diagnostic paths without substituting fixture actions,
replaying a second wrapper body, or assuming any callee correctness law.
Julia source/invariant: base/loading.jl:5225-5231
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PrecompileHintFailureEffects : Prop :=
  ∀ (X Y E D CI CF V Function FunctionType ArgTypes Signature
      Method StaticParams MethodInstance : Type)
      (o : LOps X Y E D CI CF V)
      (ops : CompilerMethodOps o Function FunctionType ArgTypes Signature Method StaticParams MethodInstance)
      (argtype : Signature) (world : World X D CI CF),
    let hintResult := StateT.run (ExceptT.run (ops.compileHint argtype)) world
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.precompile_type o ops argtype)) world
    let reachedEffects : Prop :=
      match hintResult with
      | some (.ok rawFlag, hintWorld) =>
          rawFlag.val = 0 →
            let warningResult := StateT.run (ExceptT.run ops.warningsEnabled) hintWorld
            let diagnosticEffects : Prop :=
              match warningResult with
              | some (.ok true, warningWorld) =>
                  match StateT.run (ExceptT.run (ops.warnInactive argtype)) warningWorld with
                  | none => observed = none
                  | some (.error error, finalWorld) =>
                      observed = some (.error error, finalWorld)
                  | some (.ok (), finalWorld) =>
                      observed = some (.ok false, finalWorld)
              | _ => True
            FailedHintEffectPreserved warningResult observed ∧ diagnosticEffects
      | _ => True
    FailedHintEffectPreserved hintResult observed ∧ reachedEffects

end JuliaLean.Proofs.base.loading.Models1Group10

namespace JuliaLean.Proofs.base.loading

open JuliaLean.Registry

open JuliaLean JuliaLean.base.loading

-- Helper for __precompile__
private theorem precompile_run {X Y D CI CF V : Type}
    (o : LOps X Y JuliaLean.base.io.Error D CI CF V)
    (query : JuliaLean.base.io.M (World X D CI CF) (JInt .i32))
    (inc : JuliaLean.base.io.M (World X D CI CF) Bool)
    (permitted : Bool) (world : World X D CI CF) :
    StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.__precompile__ o query inc permitted)) world =
      if permitted = true then some (.ok (), world)
      else
        match query world with
        | none => none
        | some (.error (err, w')) => some (.error (.ext err), w')
        | some (.ok (flag, w')) =>
            if flag.val == 0 then some (.ok (), w')
            else some (.error .precompilableError, w') := by
  cases permitted with
  | true => rfl
  | false =>
      simp only [JuliaLean.base.loading.Models1Group10.__precompile__,
        JuliaLean.base.loading.Models1Group10.liftIO,
        JuliaLean.base.runtime_internals.generatingOutput, throwL,
        Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        ExceptT.run, ExceptT.mk, StateT.run, StateT.mk, Bind.bind, ExceptT.bind,
        ExceptT.bindCont, StateT.bind, Option.bind, Pure.pure, ExceptT.pure,
        throw, throwThe, MonadExceptOf.throw]
      cases query world with
      | none => rfl
      | some res =>
          cases res with
          | error p => rfl
          | ok p =>
              rcases p with ⟨flag, w'⟩
              dsimp only
              cases flag.val == 0 <;> rfl

-- 9. models1-g10-precompile-admission
theorem precompileAdmission_proven :
    Models1Group10.PrecompileAdmission := by
  intro X Y D CI CF V o world outputFlag optionsIncremental permitted
  dsimp only
  rw [precompile_run]
  cases permitted with
  | true => simp
  | false =>
      have hpure : (pure outputFlag : JuliaLean.base.io.M (World X D CI CF) (JInt .i32)) world =
          some (.ok (outputFlag, world)) := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, hpure]
      by_cases hz : outputFlag.val = 0
      · simp [hz]
      · have hbeq : (outputFlag.val == 0) = false := beq_eq_false_iff_ne.mpr hz
        simp [hz, hbeq]

-- 10. models1-g10-precompile-permitted-no-query
theorem precompilePermittedNoQuery_proven :
    Models1Group10.PrecompilePermittedDoesNotObserveRuntime := by
  intro X Y D CI CF V o world outputQuery optionsIncremental
  rfl

-- 11. models1-g10-precompile-runtime-effects
theorem precompileRuntimeFailurePreserved_proven :
    Models1Group10.PrecompileRuntimeFailurePreserved := by
  intro X Y D CI CF V o world outputQuery optionsIncremental
  dsimp only
  rw [precompile_run]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases outputQuery world with
  | none => rfl
  | some res =>
      cases res with
      | error p => rfl
      | ok p =>
          rcases p with ⟨flag, nextWorld⟩
          dsimp only
          by_cases hz : flag.val = 0
          · have hbeq : (flag.val == 0) = true := beq_iff_eq.mpr hz
            rw [hbeq]
            exact And.intro
              (Iff.intro (fun _ => hz) (fun _ => rfl))
              (Iff.intro (fun h => nomatch h) (fun hne => False.elim (hne hz)))
          · have hbeq : (flag.val == 0) = false := beq_eq_false_iff_ne.mpr hz
            rw [hbeq]
            exact And.intro
              (Iff.intro (fun h => nomatch h) (fun h => False.elim (hz h)))
              (Iff.intro (fun _ => hz) (fun _ => rfl))

-- Helper for precompile_type
private theorem precompile_type_run {X Y E D CI CF V Function FunctionType ArgTypes Signature
    Method StaticParams MethodInstance : Type}
    (o : LOps X Y E D CI CF V)
    (ops : CompilerMethodOps o Function FunctionType ArgTypes Signature Method StaticParams MethodInstance)
    (argtype : Signature) (world : World X D CI CF) :
    StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.precompile_type o ops argtype)) world =
      match StateT.run (ExceptT.run (ops.compileHint argtype)) world with
      | none => none
      | some (.error err, w1) => some (.error err, w1)
      | some (.ok rawFlag, w1) =>
          if rawFlag.val = 0 then
            match StateT.run (ExceptT.run ops.warningsEnabled) w1 with
            | none => none
            | some (.error err, w2) => some (.error err, w2)
            | some (.ok false, w2) => some (.ok false, w2)
            | some (.ok true, w2) =>
                match StateT.run (ExceptT.run (ops.warnInactive argtype)) w2 with
                | none => none
                | some (.error err, w3) => some (.error err, w3)
                | some (.ok (), w3) => some (.ok false, w3)
          else some (.ok true, w1) := by
  unfold JuliaLean.base.loading.Models1Group10.precompile_type
  rw [lm_bind_run]
  cases StateT.run (ExceptT.run (ops.compileHint argtype)) world with
  | none => rfl
  | some p =>
      rcases p with ⟨res, w1⟩
      cases res with
      | error _ => rfl
      | ok rawFlag =>
          dsimp only
          rw [eq_i32_i64_zero]
          by_cases hz : rawFlag.val = 0
          · simp only [hz, decide_true, Bool.not_true, Bool.not_false, ↓reduceIte, lm_bind_run]
            cases StateT.run (ExceptT.run ops.warningsEnabled) w1 with
            | none => rfl
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                cases res2 with
                | error _ => rfl
                | ok warn =>
                    cases warn with
                    | false => rfl
                    | true =>
                        simp only [↓reduceIte, lm_bind_run]
                        cases StateT.run (ExceptT.run (ops.warnInactive argtype)) w2 with
                        | none => rfl
                        | some p3 =>
                            rcases p3 with ⟨res3, w3⟩
                            cases res3 <;> rfl
          · simp only [hz, decide_false, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rfl

-- 12. models1-g10-precompile-hint-flag
theorem precompileHintFlagResult_proven :
    Models1Group10.PrecompileHintFlagResult := by
  intro X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance
    o ops argtype world
  dsimp only
  rw [precompile_type_run]
  cases StateT.run (ExceptT.run (ops.compileHint argtype)) world with
  | none => trivial
  | some p =>
      rcases p with ⟨res, w1⟩
      cases res with
      | error _ => trivial
      | ok rawFlag =>
          dsimp only
          by_cases hz : rawFlag.val = 0
          · simp only [hz, ↓reduceIte]
            cases StateT.run (ExceptT.run ops.warningsEnabled) w1 with
            | none => trivial
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                cases res2 with
                | error _ => trivial
                | ok warn =>
                    cases warn with
                    | false => simp [hz]
                    | true =>
                        dsimp only
                        cases StateT.run (ExceptT.run (ops.warnInactive argtype)) w2 with
                        | none => trivial
                        | some p3 =>
                            rcases p3 with ⟨res3, w3⟩
                            cases res3 with
                            | error _ => trivial
                            | ok _ => simp [hz]
          · simp [hz]

-- 13. models1-g10-precompile-hint-success
theorem precompileHintSuccessSkipsWarnings_proven :
    Models1Group10.PrecompileHintSuccessSkipsWarnings := by
  intro X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance
    o ops argtype world
  rw [precompile_type_run]
  cases StateT.run (ExceptT.run (ops.compileHint argtype)) world with
  | none => trivial
  | some p =>
      rcases p with ⟨res, nextWorld⟩
      cases res with
      | error _ => trivial
      | ok rawFlag =>
          intro hnz
          simp only [hnz, ↓reduceIte]

-- 14. models1-g10-precompile-hint-disabled
theorem precompileHintDisabledWarningsSkipLogger_proven :
    Models1Group10.PrecompileHintDisabledWarningsSkipLogger := by
  intro X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance
    o ops argtype world
  dsimp only
  rw [precompile_type_run]
  cases StateT.run (ExceptT.run (ops.compileHint argtype)) world with
  | none => trivial
  | some p =>
      rcases p with ⟨res, hintWorld⟩
      cases res with
      | error _ => trivial
      | ok rawFlag =>
          intro hz
          simp only [hz, ↓reduceIte]
          cases StateT.run (ExceptT.run ops.warningsEnabled) hintWorld with
          | none => trivial
          | some p2 =>
              rcases p2 with ⟨res2, warningWorld⟩
              cases res2 with
              | error _ => trivial
              | ok warn =>
                  cases warn with
                  | false => rfl
                  | true => trivial

-- 15. models1-g10-precompile-hint-failures
theorem precompileHintFailureEffects_proven :
    Models1Group10.PrecompileHintFailureEffects := by
  intro X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance
    o ops argtype world
  dsimp only
  unfold Models1Group10.FailedHintEffectPreserved
  rw [precompile_type_run]
  cases StateT.run (ExceptT.run (ops.compileHint argtype)) world with
  | none => exact ⟨rfl, trivial⟩
  | some p =>
      rcases p with ⟨res, hintWorld⟩
      cases res with
      | error _ => exact ⟨rfl, trivial⟩
      | ok rawFlag =>
          refine ⟨trivial, fun hz => ?_⟩
          simp only [hz, ↓reduceIte]
          cases StateT.run (ExceptT.run ops.warningsEnabled) hintWorld with
          | none => exact ⟨rfl, trivial⟩
          | some p2 =>
              rcases p2 with ⟨res2, warningWorld⟩
              cases res2 with
              | error _ => exact ⟨rfl, trivial⟩
              | ok warn =>
                  cases warn with
                  | false => exact ⟨trivial, trivial⟩
                  | true =>
                      refine ⟨trivial, ?_⟩
                      dsimp only
                      cases StateT.run (ExceptT.run (ops.warnInactive argtype)) warningWorld with
                      | none => rfl
                      | some p3 =>
                          rcases p3 with ⟨res3, finalWorld⟩
                          cases res3 <;> rfl


def entriesModels1Group10 : List Entry := [
  { id := "loading-precompile-admission", juliaFile := "base/loading.jl"
    juliaFns := ["__precompile__(::Bool)"]
    statement := "The declaration accepts permitted files and ordinary evaluation, and rejects a non-precompilable file during either package or system-image output generation, without filtering on incremental mode."
    source := "base/loading.jl:2795-2808; base/runtime_internals.jl:1829-1847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.PrecompileAdmission
    thm := some ``JuliaLean.Proofs.base.loading.precompileAdmission_proven
    notes := "Additive group-10 model; unproved statement. Compiler validation unavailable in this environment; see NOTES.md." },
  { id := "loading-precompile-permitted-no-query", juliaFile := "base/loading.jl"
    juliaFns := ["__precompile__(::Bool)"]
    statement := "Declaring a file precompilable returns nothing with unchanged state and does not execute either runtime observation, even if those observations would fail or diverge."
    source := "base/loading.jl:2795-2808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.PrecompilePermittedDoesNotObserveRuntime
    thm := some ``JuliaLean.Proofs.base.loading.precompilePermittedNoQuery_proven
    notes := "Additive group-10 model; unproved statement. Compiler validation unavailable in this environment; see NOTES.md." },
  { id := "loading-precompile-runtime-effects", juliaFile := "base/loading.jl"
    juliaFns := ["__precompile__(::Bool)"]
    statement := "For a file that refuses precompilation, the runtime query determines admission; its errors, nontermination, and post-action state are preserved, and nonzero output-generation status raises PrecompilableError."
    source := "base/loading.jl:2803-2808; base/runtime_internals.jl:1841-1847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.PrecompileRuntimeFailurePreserved
    thm := some ``JuliaLean.Proofs.base.loading.precompileRuntimeFailurePreserved_proven
    notes := "Additive group-10 model; unproved statement. Compiler validation unavailable in this environment; see NOTES.md." },
  { id := "loading-precompile-hint-flag", juliaFile := "base/loading.jl"
    juliaFns := ["precompile(::Type)"]
    statement := "For all original runtime operations and signatures, whenever the compiler hint and wrapper return normally, the returned Bool is true exactly when the observed Int32 status is nonzero."
    source := "base/loading.jl:5225-5231 (wrapper invariant); base/loading.jl:5215-5222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.PrecompileHintFlagResult
    thm := some ``JuliaLean.Proofs.base.loading.precompileHintFlagResult_proven
    notes := "Additive group-10 model; unproved statement. Compiler validation unavailable in this environment; see NOTES.md." },
  { id := "loading-precompile-hint-success", juliaFile := "base/loading.jl"
    juliaFns := ["precompile(::Type)"]
    statement := "A successful compile-hint observation returns true in its actual post-hint world without reading the warning flag or invoking the logger, including when those unused actions would mutate, fail or diverge."
    source := "base/loading.jl:5225-5231 (wrapper invariant); base/loading.jl:5215-5222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.PrecompileHintSuccessSkipsWarnings
    thm := some ``JuliaLean.Proofs.base.loading.precompileHintSuccessSkipsWarnings_proven
    notes := "Additive group-10 model; unproved statement. Compiler validation unavailable in this environment; see NOTES.md." },
  { id := "loading-precompile-hint-disabled", juliaFile := "base/loading.jl"
    juliaFns := ["precompile(::Type)"]
    statement := "After an actual zero-status hint, a warning read in the actual post-hint world that returns false causes the wrapper to return false in the post-read world without invoking an arbitrary logger."
    source := "base/loading.jl:5225-5231 (wrapper invariant); base/loading.jl:5215-5222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.PrecompileHintDisabledWarningsSkipLogger
    thm := some ``JuliaLean.Proofs.base.loading.precompileHintDisabledWarningsSkipLogger_proven
    notes := "Additive group-10 model; unproved statement. Compiler validation unavailable in this environment; see NOTES.md." },
  { id := "loading-precompile-hint-failures", juliaFile := "base/loading.jl"
    juliaFns := ["precompile(::Type)"]
    statement := "The wrapper preserves exceptions, post-error worlds and nontermination from each reached operation in the state produced by its predecessors; a successful enabled diagnostic returns false and retains the diagnostic final world."
    source := "base/loading.jl:5225-5231 (wrapper invariant); base/loading.jl:5215-5222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.PrecompileHintFailureEffects
    thm := some ``JuliaLean.Proofs.base.loading.precompileHintFailureEffects_proven
    notes := "Additive group-10 model; unproved statement. Compiler validation unavailable in this environment; see NOTES.md." }
]

end JuliaLean.Proofs.base.loading

namespace JuliaLean.Proofs.base.loading.Models1Group10

open JuliaLean
open JuliaLean.base.loading
open JuliaLean.base.loading.Models1Group10

/-- Failure of opening the cache must escape unchanged, without cleanup or reads.
All paths, worlds and primitive actions are retained. Source: base/loading.jl:2324-2341. -/
def CacheBuildIdOpenFailure : Prop :=
  ∀ (X Y D CI CF V Stream Vector Lock : Type)
    (o : LOps X Y JuliaLean.base.io.Error D CI CF V)
    (ops : CacheIOOps o Stream)
    (access : JuliaLean.base.iostream.Access (World X D CI CF) Stream Vector Lock)
    (locks : JuliaLean.base.iostream.Locks (World X D CI CF) Lock)
    (runtime : JuliaLean.base.iostream.Runtime (World X D CI CF) Vector)
    (systemerror : String → Bool → JuliaLean.base.io.M (World X D CI CF) Unit)
    (path : Bytes) (world : World X D CI CF),
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.parse_cache_buildid o ops access locks runtime systemerror path)) world
    match StateT.run (ExceptT.run (ops.openRead path)) world with
    | none => observed = none
    | some (.error error, next) => observed = some (.error error, next)
    | some (.ok _, _) => True

/-- Construction allocates a new cell with absent fields, preserves every old cell,
and leaves the registry and loading world unchanged. Source: base/loading.jl:3027-3032. -/
def OriginAllocationFresh : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V)
    (world : OriginState X D CI CF V),
    ∃ (ref : OriginRef) (next : OriginState X D CI CF V),
      StateT.run (ExceptT.run
        (JuliaLean.base.loading.Models1Group10.PkgOrigin_new o)) world = some (.ok ref, next) ∧
      ¬ OriginRefValid world ref ∧ OriginRefValid next ref ∧
      next.objects.length = world.objects.length + 1 ∧
      (∀ (index : Nat), index < world.objects.length →
        next.objects[index]? = world.objects[index]?) ∧
      (∃ cell, next.objects[ref.slot]? = some cell ∧
        cell.path = none ∧ cell.cachepath = none ∧ cell.version = none) ∧
      next.loading = world.loading ∧ next.pkgorigins = world.pkgorigins

/-- A failing initial registry observation is never swallowed; unlocking preserves
its error and all other post-error state. Source: base/loading.jl:3056-3075. -/
def RootRegistrationLookupFailure : Prop :=
  ∀ (X Y D CI CF V Mod : Type)
    (o : LOps X Y JuliaLean.base.io.Error D CI CF V)
    (ops : ModuleRegistryOps o Mod)
    (query : JuliaLean.base.io.M (World X D CI CF) (JInt .i32))
    (incremental : JuliaLean.base.io.M (World X D CI CF) Bool)
    (m : Mod) (world : World X D CI CF),
    let key := JuliaLean.base.pkgid.PkgId_Module ops.moduleUuid
      (fun module => ops.moduleName (ops.moduleroot module)) m (some (ops.moduleName m))
    let locked := {world with require_lock := world.require_lock + 1}
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.register_root_module o ops query incremental m)) world
    match StateT.run (ExceptT.run (ops.loadedModule key)) locked with
    | none => observed = none
    | some (.error error, next) =>
        observed = some (.error error, {next with require_lock := next.require_lock - 1})
    | some (.ok _, _) => True

/-- A module already present is not registered again. Its successful lookup's
post-world is retained, even if subsequent runtime actions would fail or diverge.
Source: base/loading.jl:3079-3083. -/
def ReusedModulePresentSkipsRegistration : Prop :=
  ∀ (X Y D CI CF V Mod : Type)
    (o : LOps X Y JuliaLean.base.io.Error D CI CF V)
    (ops : ModuleRegistryOps o Mod)
    (query : JuliaLean.base.io.M (World X D CI CF) (JInt .i32))
    (incremental : JuliaLean.base.io.M (World X D CI CF) Bool)
    (m : Mod) (world : World X D CI CF),
    match StateT.run (ExceptT.run (maybe_root_module o ops (root_module_key ops m))) world with
    | some (.ok (some _), next) =>
        StateT.run (ExceptT.run
          (JuliaLean.base.loading.Models1Group10.register_reused_module o ops query incremental m)) world =
          some (.ok false, next)
    | _ => True

/-- Removing an absent module does not pop an entry or touch the module-order
array. The lookup's world is retained apart from unlocking. Source: base/loading.jl:3115-3123. -/
def UnreferenceAbsentSkipsPop : Prop :=
  ∀ (X Y E D CI CF V Mod : Type) (o : LOps X Y E D CI CF V)
    (ops : ModuleRegistryOps o Mod) (key : JuliaLean.base.pkgid.PkgId)
    (world : World X D CI CF),
    match StateT.run (ExceptT.run (ops.loadedModule key))
      {world with require_lock := world.require_lock + 1} with
    | some (.ok none, next) =>
        StateT.run (ExceptT.run
          (JuliaLean.base.loading.Models1Group10.unreference_module o ops key)) world =
          some (.ok none, {next with require_lock := next.require_lock - 1})
    | _ => True

/-- A failed first global observation cannot become a default trace setting.
Source: base/loading.jl:3421-3430. -/
def TraceObservationFailurePreserved : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V)
    (runtime : TraceEvalRuntime o) (world : World X D CI CF),
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.current_trace_eval_level o runtime)) world
    match StateT.run (ExceptT.run runtime.traceEval) world with
    | none => observed = none
    | some (.error error, next) => observed = some (.error error, next)
    | some (.ok _, _) => True

/-- An empty current stack formats as empty bytes, preserving the read's state
without consulting any formatting callback. Source: base/loading.jl:3772-3778. -/
def EmptyNestedPrecompList : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V)
    (ops : NestedPrecompOps o) (world : World X D CI CF),
    match StateT.run (ExceptT.run ops.stack) world with
    | some (.ok [], next) =>
        StateT.run (ExceptT.run
          (JuliaLean.base.loading.Models1Group10.nested_precomp_list o ops)) world = some (.ok [], next)
    | _ => True

/-- File identities retain both timestamps exactly, including NaNs and signed
zeros, without numerical equality replacing value identity. Source: base/loading.jl:4061. -/
def IdentityTimestampsPreserved : Prop :=
  ∀ (stat : CacheFileStat),
    let identity := JuliaLean.base.loading.Models1Group10.file_identity stat
    identity.2.2.2.1 = stat.mtime ∧ identity.2.2.2.2 = stat.ctime

/-- A failed object stat happens before the stream stat and escapes with its
post-error world. Source: base/loading.jl:4063-4066. -/
def ChecksumObjectStatFailure : Prop :=
  ∀ (X Y E D CI CF V Stream : Type) (o : LOps X Y E D CI CF V)
    (ops : CacheIOOps o Stream) (stream : Stream) (path : Bytes)
    (world : World X D CI CF),
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.checksum_key o ops stream (some path))) world
    match StateT.run (ExceptT.run (ops.statPath path)) world with
    | none => observed = none
    | some (.error error, next) => observed = some (.error error, next)
    | some (.ok _, _) => True

/-- Combined-checksum mode skips all validation only for a native-image cache.
All primitive operations, reasons and states are quantified, including actions
that would mutate, fail or diverge. Source: base/loading.jl:4068-4083. -/
def CombinedChecksumSkip : Prop :=
  ∀ (X Y E D CI CF V Stream : Type) (slots : Nat)
    (o : LOps X Y E D CI CF V) (ops : CacheIOOps o Stream)
    (logging : ChecksumLogging o slots) (stream : Stream) (cachefile objectfile : Bytes)
    (reasons : ChecksumReasons slots) (world : ChecksumState X D CI CF slots),
    StateT.run (ExceptT.run
      (checksums_invalid_io o ops logging stream cachefile (some objectfile) reasons false)) world =
      some (.ok false, world)

/-- Path derivation precedes the IO-error handler. Its failures and divergence
must escape without becoming false or losing any world state. Source: base/loading.jl:4119-4133. -/
def ChecksumNowPathFailure : Prop :=
  ∀ (X Y E D CI CF V Stream : Type) (slots : Nat)
    (o : LOps X Y (ChecksumExternalError E) D CI CF V)
    (ops : CacheIOOps o Stream) (logging : ChecksumLogging o slots)
    (candidates : CacheCandidateOps o)
    (dictCarrier : JuliaLean.base.set.DictRuntime ChecksumKey)
    (tupleCarrier : JuliaLean.base.tuple.Ops FileIdentity)
    (layout : ChecksumKeyLayout) (path : JuliaLean.Strings.JStr)
    (world : ChecksumState X D CI CF slots),
    let observed := StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.checksums_valid_now o ops logging candidates
        dictCarrier tupleCarrier layout path)) world
    match StateT.run (ExceptT.run (checksumObjectCachePath o candidates path)) world.loading with
    | none => observed = none
    | some (.error error, next) => observed = some (.error error, {world with loading := next})
    | some (.ok _, _) => True

end JuliaLean.Proofs.base.loading.Models1Group10

namespace JuliaLean.Proofs.base.loading

open JuliaLean.Registry

open JuliaLean JuliaLean.base.loading

-- 16. models1-g10-cache-buildid-open-failure
theorem cacheBuildIdOpenFailure_proven :
    Models1Group10.CacheBuildIdOpenFailure := by
  intro X Y D CI CF V Stream Vector Lock o ops access locks runtime systemerror path world
  dsimp only
  rw [JuliaLean.base.loading.Models1Group10.parse_cache_buildid.eq_def, lm_bind_run]
  cases StateT.run (ExceptT.run (ops.openRead path)) world with
  | none => rfl
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error _ => rfl
      | ok _ => trivial

-- 17. models1-g10-origin-allocation-fresh
theorem originAllocationFresh_proven :
    Models1Group10.OriginAllocationFresh := by
  intro X Y E D CI CF V o world
  refine ⟨⟨world.objects.length⟩,
    { world with objects := world.objects ++ [JuliaLean.base.loading.PkgOrigin_new] },
    rfl, ?_, ?_, List.length_append, ?_, ?_, rfl, rfl⟩
  · unfold JuliaLean.base.loading.Models1Group10.OriginRefValid
    exact Nat.lt_irrefl _
  · unfold JuliaLean.base.loading.Models1Group10.OriginRefValid
    simp [List.length_append]
  · intro index hlt
    exact List.getElem?_append_left hlt
  · refine ⟨JuliaLean.base.loading.PkgOrigin_new, ?_, rfl, rfl, rfl⟩
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

-- 18. models1-g10-root-registration-lookup-failure
theorem rootRegistrationLookupFailure_proven :
    Models1Group10.RootRegistrationLookupFailure := by
  intro X Y D CI CF V Mod o ops query incremental m world
  dsimp only
  rw [JuliaLean.base.loading.Models1Group10.register_root_module.eq_def,
    lm_withLock_run, lm_bind_run]
  cases StateT.run (ExceptT.run (ops.loadedModule
      (JuliaLean.base.pkgid.PkgId_Module ops.moduleUuid
        (fun module => ops.moduleName (ops.moduleroot module)) m (some (ops.moduleName m)))))
      { world with require_lock := world.require_lock + 1 } with
  | none => rfl
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error _ => rfl
      | ok _ => trivial

-- 19. models1-g10-reused-module-present
theorem reusedModulePresentSkipsRegistration_proven :
    Models1Group10.ReusedModulePresentSkipsRegistration := by
  intro X Y D CI CF V Mod o ops query incremental m world
  rw [JuliaLean.base.loading.Models1Group10.register_reused_module.eq_def, lm_bind_run]
  cases StateT.run (ExceptT.run (maybe_root_module o ops (root_module_key ops m))) world with
  | none => trivial
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error _ => trivial
      | ok opt =>
          cases opt with
          | none => trivial
          | some _ => rfl

-- 20. models1-g10-unreference-absent
theorem unreferenceAbsentSkipsPop_proven :
    Models1Group10.UnreferenceAbsentSkipsPop := by
  intro X Y E D CI CF V Mod o ops key world
  rw [JuliaLean.base.loading.Models1Group10.unreference_module.eq_def,
    lm_withLock_run, lm_bind_run]
  cases StateT.run (ExceptT.run (ops.loadedModule key))
      { world with require_lock := world.require_lock + 1 } with
  | none => trivial
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error _ => trivial
      | ok opt =>
          cases opt with
          | none => rfl
          | some _ => trivial

-- 21. models1-g10-trace-observation-failure
theorem traceObservationFailurePreserved_proven :
    Models1Group10.TraceObservationFailurePreserved := by
  intro X Y E D CI CF V o runtime world
  dsimp only
  rw [JuliaLean.base.loading.Models1Group10.current_trace_eval_level.eq_def, lm_bind_run]
  cases StateT.run (ExceptT.run runtime.traceEval) world with
  | none => rfl
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error _ => rfl
      | ok _ => trivial

-- 22. models1-g10-empty-nested-precomp-list
theorem emptyNestedPrecompList_proven :
    Models1Group10.EmptyNestedPrecompList := by
  intro X Y E D CI CF V o ops world
  rw [JuliaLean.base.loading.Models1Group10.nested_precomp_list.eq_def, lm_bind_run]
  cases StateT.run (ExceptT.run ops.stack) world with
  | none => trivial
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error _ => trivial
      | ok st =>
          cases st with
          | nil => rfl
          | cons _ _ => trivial

-- 23. models1-g10-identity-timestamps
theorem identityTimestampsPreserved_proven :
    Models1Group10.IdentityTimestampsPreserved := by
  intro stat
  exact ⟨rfl, rfl⟩

-- 24. models1-g10-checksum-object-stat-failure
theorem checksumObjectStatFailure_proven :
    Models1Group10.ChecksumObjectStatFailure := by
  intro X Y E D CI CF V Stream o ops stream path world
  dsimp only
  rw [JuliaLean.base.loading.Models1Group10.checksum_key.eq_def, lm_bind_run]
  cases StateT.run (ExceptT.run (ops.statPath path)) world with
  | none => rfl
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error _ => rfl
      | ok _ => trivial

-- 25. models1-g10-combined-checksum-skip
theorem combinedChecksumSkip_proven :
    Models1Group10.CombinedChecksumSkip := by
  intro X Y E D CI CF V Stream slots o ops logging stream cachefile objectfile reasons world
  rfl

-- 26. models1-g10-checksum-now-path-failure
private theorem checksumM_bind_lift_run {X Y E D CI CF V α β : Type} {slots : Nat}
    {o : LOps X Y E D CI CF V}
    (act : LM o α) (f : α → JuliaLean.base.loading.Models1Group10.ChecksumM o slots β)
    (world : JuliaLean.base.loading.Models1Group10.ChecksumState X D CI CF slots) :
    StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.liftChecksumLoading o act >>= f)) world =
      match StateT.run (ExceptT.run act) world.loading with
      | none => none
      | some (.error e, next) => some (.error e, { world with loading := next })
      | some (.ok a, next) => StateT.run (ExceptT.run (f a)) { world with loading := next } := by
  simp only [JuliaLean.base.loading.Models1Group10.liftChecksumLoading,
    ExceptT.run, StateT.run, StateT.mk, Bind.bind, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, StateT.bind, Option.bind]
  cases act world.loading with
  | none => rfl
  | some p => rcases p with ⟨r, next⟩; cases r <;> rfl

private theorem checksumM_bind_lift_none {X Y E D CI CF V α β : Type} {slots : Nat}
    {o : LOps X Y E D CI CF V}
    (act : LM o α) (f : α → JuliaLean.base.loading.Models1Group10.ChecksumM o slots β)
    (world : JuliaLean.base.loading.Models1Group10.ChecksumState X D CI CF slots)
    (h : StateT.run (ExceptT.run act) world.loading = none) :
    StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.liftChecksumLoading o act >>= f)) world = none := by
  rw [checksumM_bind_lift_run, h]

private theorem checksumM_bind_lift_error {X Y E D CI CF V α β : Type} {slots : Nat}
    {o : LOps X Y E D CI CF V}
    (act : LM o α) (f : α → JuliaLean.base.loading.Models1Group10.ChecksumM o slots β)
    (world : JuliaLean.base.loading.Models1Group10.ChecksumState X D CI CF slots)
    (err : LErr E) (next : World X D CI CF)
    (h : StateT.run (ExceptT.run act) world.loading = some (.error err, next)) :
    StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.liftChecksumLoading o act >>= f)) world =
      some (.error err, { world with loading := next }) := by
  rw [checksumM_bind_lift_run, h]

theorem checksumNowPathFailure_proven :
    Models1Group10.ChecksumNowPathFailure := by
  intro X Y E D CI CF V Stream slots o ops logging candidates dictCarrier tupleCarrier layout path world
  intro observed
  cases hstep : StateT.run (ExceptT.run
      (JuliaLean.base.loading.Models1Group10.checksumObjectCachePath o candidates path))
      world.loading with
  | none => exact checksumM_bind_lift_none _ _ world hstep
  | some p =>
      rcases p with ⟨res, next⟩
      cases res with
      | error err => exact checksumM_bind_lift_error _ _ world err next hstep
      | ok _ => trivial

def entriesModels1Group10Coverage : List Entry := [
  { id := "loading-cache-buildid-open-failure", juliaFile := "base/loading.jl"
    juliaFns := ["parse_cache_buildid(cachepath::String)"]
    statement := "Opening a cache that fails or diverges does not execute reads or cleanup and preserves its failure state."
    source := "base/loading.jl:2324-2341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.CacheBuildIdOpenFailure
    thm := some ``JuliaLean.Proofs.base.loading.cacheBuildIdOpenFailure_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-origin-allocation-fresh", juliaFile := "base/loading.jl"
    juliaFns := ["PkgOrigin()"]
    statement := "Constructing PkgOrigin allocates a fresh all-nothing cell, preserves all existing cells and leaves registry and loading state unchanged."
    source := "base/loading.jl:3032-3032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.OriginAllocationFresh
    thm := some ``JuliaLean.Proofs.base.loading.originAllocationFresh_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-root-registration-lookup-failure", juliaFile := "base/loading.jl"
    juliaFns := ["register_root_module(m::Module)"]
    statement := "A failing first registry lookup escapes unchanged except for releasing the acquired lock."
    source := "base/loading.jl:3056-3075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.RootRegistrationLookupFailure
    thm := some ``JuliaLean.Proofs.base.loading.rootRegistrationLookupFailure_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-reused-module-present", juliaFile := "base/loading.jl"
    juliaFns := ["register_reused_module(m::Module)"]
    statement := "An already present reused module returns false without attempting registration and retains the lookup post-state."
    source := "base/loading.jl:3079-3083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.ReusedModulePresentSkipsRegistration
    thm := some ``JuliaLean.Proofs.base.loading.reusedModulePresentSkipsRegistration_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-unreference-absent", juliaFile := "base/loading.jl"
    juliaFns := ["unreference_module(key::PkgId)"]
    statement := "An absent module returns nothing without a pop or module-order access, preserving the lookup post-state apart from unlocking."
    source := "base/loading.jl:3115-3123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.UnreferenceAbsentSkipsPop
    thm := some ``JuliaLean.Proofs.base.loading.unreferenceAbsentSkipsPop_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-trace-observation-failure", juliaFile := "base/loading.jl"
    juliaFns := ["current_trace_eval_level()"]
    statement := "Failure or divergence of the first TRACE_EVAL observation cannot be replaced by a default trace setting."
    source := "base/loading.jl:3421-3430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.TraceObservationFailurePreserved
    thm := some ``JuliaLean.Proofs.base.loading.traceObservationFailurePreserved_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-empty-nested-precomp-list", juliaFile := "base/loading.jl"
    juliaFns := ["list()"]
    statement := "An empty live precompilation stack formats as empty bytes with the actual stack-read post-state."
    source := "base/loading.jl:3775-3775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.EmptyNestedPrecompList
    thm := some ``JuliaLean.Proofs.base.loading.emptyNestedPrecompList_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-identity-timestamps", juliaFile := "base/loading.jl"
    juliaFns := ["file_identity(st::StatStruct)"]
    statement := "File identities retain both timestamp values exactly, including NaNs and signed zeros."
    source := "base/loading.jl:4061-4061 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.IdentityTimestampsPreserved
    thm := some ``JuliaLean.Proofs.base.loading.identityTimestampsPreserved_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-checksum-object-stat-failure", juliaFile := "base/loading.jl"
    juliaFns := ["checksum_key(io::IOStream, ocachefile::Union{Nothing, String})"]
    statement := "An object-stat failure occurs before stream stat and escapes with its original error and post-state."
    source := "base/loading.jl:4063-4066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.ChecksumObjectStatFailure
    thm := some ``JuliaLean.Proofs.base.loading.checksumObjectStatFailure_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-combined-checksum-skip", juliaFile := "base/loading.jl"
    juliaFns := ["checksums_invalid(io::IOStream, cachefile::String, ocachefile::Union{Nothing, String}, reasons; split_checksums::Bool=true)"]
    statement := "Combined-checksum mode with a native image skips all validations and returns false without any state changes."
    source := "base/loading.jl:4070-4083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.CombinedChecksumSkip
    thm := some ``JuliaLean.Proofs.base.loading.combinedChecksumSkip_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." },
  { id := "loading-checksum-now-path-failure", juliaFile := "base/loading.jl"
    juliaFns := ["checksums_valid_now(cachefile::String)"]
    statement := "Object-cache path derivation occurs outside the IO-error catch and preserves any failure or divergence."
    source := "base/loading.jl:4119-4133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven
    prop := ``JuliaLean.Proofs.base.loading.Models1Group10.ChecksumNowPathFailure
    thm := some ``JuliaLean.Proofs.base.loading.checksumNowPathFailure_proven
    notes := "Independent invariant added during scratch preparation; unchecked. Runtime and representation boundaries remain explicit." }
]

end JuliaLean.Proofs.base.loading

namespace JuliaLean.Proofs.base.loading.Models2Group4
open JuliaLean JuliaLean.Registry
open JuliaLean.base.loading.Models2Group4

/-- ExceptT outside StateT retains mutations on failure; none is divergence. -/
abbrev ObservationM (E W : Type) (A : Type) := ExceptT (DispatchError E) (StateT W Option) A

def observe {E W A : Type} (action : ObservationM E W A) (world : W) :
    Option (Except (DispatchError E) A × W) :=
  StateT.run (ExceptT.run action) world

/-- Independent class specification; does not call the model's classifier. -/
def IsIOError {E : Type} (error : DispatchError E) : Prop :=
  ∃ value, error = .ioError value

/-- Transparency of an exception filter to successful values, other exceptions,
mutation and divergence; IOErrors yield false without undoing effects. The
observations range over arbitrary selected callees without correctness laws.
This relation on terminal observations is not another executable body. -/
def FilterInvariant {E W Other : Type}
    (source filtered : Option (Except (DispatchError E) (DispatchValue Other) × W)) : Prop :=
  (source = none ↔ filtered = none) ∧
  source.map (fun observation => observation.2) =
    filtered.map (fun observation => observation.2) ∧
  (∀ value finalWorld, source = some (.ok value, finalWorld) →
    filtered = some (.ok value, finalWorld)) ∧
  (∀ error finalWorld, source = some (.error error, finalWorld) →
    (IsIOError error → filtered = some (.ok (.bool false), finalWorld)) ∧
    (¬ IsIOError error → filtered = some (.error error, finalWorld))) ∧
  (∀ error finalWorld, filtered = some (.error error, finalWorld) → ¬ IsIOError error)

/-- Open dispatch may alter W but cannot forge this separate log. -/
inductive CallEvent (P Long Left Right : Type) where
  | isdir (path : P)
  | isfile (path : P)
  | ispath (path : P)
  | customAccessibleFile (path : P)
  | longpath (path : P)
  | basenameLong (value : Long)
  | basenamePath (path : P)
  | equal (left : Left) (right : Right)

/-- Instrument one arbitrary action without changing its result/error/world.
Completed calls retain the event even on error; divergence remains none. -/
def record {E W A Event : Type} (event : Event) (action : ObservationM E W A) :
    ObservationM E (W × List Event) A :=
  ExceptT.mk (StateT.mk (fun initial => do
    let (result, finalWorld) ← observe action initial.1
    pure (result, (finalWorld, initial.2 ++ [event]))))

def tracePredicates {E W P Other Long Left Right : Type}
    (ops : FsDispatchOps (ObservationM E W) P Other) :
    FsDispatchOps (ObservationM E (W × List (CallEvent P Long Left Right))) P Other where
  isdir := fun path => record (.isdir path) (ops.isdir path)
  isfile := fun path => record (.isfile path) (ops.isfile path)
  ispath := fun path => record (.ispath path) (ops.ispath path)

def traceAccessible {E W P Other Long Left Right : Type}
    (ops : AccessibleFileOps (ObservationM E W) P Other) :
    AccessibleFileOps (ObservationM E (W × List (CallEvent P Long Left Right))) P Other where
  predicates := tracePredicates ops.predicates
  selection := ops.selection
  custom := fun path => record (.customAccessibleFile path) (ops.custom path)

def traceWindows {E W P Other Long Left Right : Type}
    (ops : WindowsCaseOps (ObservationM E W) P Other Long Left Right) :
    WindowsCaseOps (ObservationM E (W × List (CallEvent P Long Left Right)))
      P Other Long Left Right where
  accessible := traceAccessible ops.accessible
  longpath := fun path => record (.longpath path) (ops.longpath path)
  basenameLong := fun value => record (.basenameLong value) (ops.basenameLong value)
  basenamePath := fun path => record (.basenamePath path) (ops.basenamePath path)
  equal := fun left right => record (.equal left right) (ops.equal left right)

def accessibilityEvent {P Long Left Right : Type}
    (selection : AccessibleFileSelection) (path : P) : CallEvent P Long Left Right :=
  match selection with
  | .base => .isfile path
  | .custom => .customAccessibleFile path

/-- Allowed once-only, fail-fast call traces, with original path arguments.
This is an observation language, not another implementation or a callee law. -/
def WindowsTrace {P Long Left Right : Type} (selection : AccessibleFileSelection)
    (path : P) (events : List (CallEvent P Long Left Right)) : Prop :=
  events = [accessibilityEvent selection path] ∨
  events = [accessibilityEvent selection path, .longpath path] ∨
  (∃ long, events = [accessibilityEvent selection path, .longpath path,
    .basenameLong long]) ∨
  (∃ long, events = [accessibilityEvent selection path, .longpath path,
    .basenameLong long, .basenamePath path]) ∨
  (∃ long left right, events = [accessibilityEvent selection path, .longpath path,
    .basenameLong long, .basenamePath path, .equal left right])

/-- Full untyped domain, including arbitrary successful values, all errors,
mutations and divergence; exactly one isdir call uses the original argument.
No callee-correctness law is assumed.
Julia source: base/loading.jl:86-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:790-832; base/loading.jl:84. -/
def AccessibleDirCorrect : Prop :=
  ∀ (E W P Other : Type) (ops : FsDispatchOps (ObservationM E W) P Other)
      (path : P) (world : W),
    FilterInvariant (observe (ops.isdir path) world)
      (observe (isAccessibleDir (E := E) ops path) world) ∧
    (∀ result finalWorld events,
      observe (isAccessibleDir (E := E)
        (tracePredicates (Long := Unit) (Left := Unit) (Right := Unit) ops) path)
        (world, []) = some (result, (finalWorld, events)) →
      events = [CallEvent.isdir path])

/-- Full untyped domain, including arbitrary successful values, all errors,
mutations and divergence; exactly one isfile call uses the original argument.
No callee-correctness law is assumed.
Julia source: base/loading.jl:95-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:790-832; base/loading.jl:84. -/
def AccessibleFileCorrect : Prop :=
  ∀ (E W P Other : Type) (ops : FsDispatchOps (ObservationM E W) P Other)
      (path : P) (world : W),
    FilterInvariant (observe (ops.isfile path) world)
      (observe (isAccessibleFile (E := E) ops path) world) ∧
    (∀ result finalWorld events,
      observe (isAccessibleFile (E := E)
        (tracePredicates (Long := Unit) (Left := Unit) (Right := Unit) ops) path)
        (world, []) = some (result, (finalWorld, events)) →
      events = [CallEvent.isfile path])

/-- Full untyped domain, including arbitrary successful values, all errors,
mutations and divergence; exactly one ispath call uses the original argument.
No callee-correctness law is assumed.
Julia source: base/loading.jl:104-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:790-832; base/loading.jl:84. -/
def AccessiblePathCorrect : Prop :=
  ∀ (E W P Other : Type) (ops : FsDispatchOps (ObservationM E W) P Other)
      (path : P) (world : W),
    FilterInvariant (observe (ops.ispath path) world)
      (observe (isAccessiblePath (E := E) ops path) world) ∧
    (∀ result finalWorld events,
      observe (isAccessiblePath (E := E)
        (tracePredicates (Long := Unit) (Left := Unit) (Right := Unit) ops) path)
        (world, []) = some (result, (finalWorld, events)) →
      events = [CallEvent.ispath path])

/-- Unix/non-Apple makes one selected call. Base filters only IOErrors; a custom
method's entire observation, including IOError, passes through unchanged.
All types, callees and worlds are quantified without laws. This registration
also covers the actual selectedAccessibleFile helper.
Julia source: base/loading.jl:8-10,95-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:790-832. -/
def UnixCaseSensitiveCorrect : Prop :=
  ∀ (E W P Other : Type) (ops : AccessibleFileOps (ObservationM E W) P Other)
      (path : P) (world : W),
    (match ops.selection path with
      | .base => FilterInvariant (observe (ops.predicates.isfile path) world)
          (observe (isFileCaseSensitiveUnix (E := E) ops path) world)
      | .custom =>
          observe (isFileCaseSensitiveUnix (E := E) ops path) world =
            observe (ops.custom path) world) ∧
    (∀ result finalWorld events,
      observe (isFileCaseSensitiveUnix (E := E)
        (traceAccessible (Long := Unit) (Left := Unit) (Right := Unit) ops) path)
        (world, []) = some (result, (finalWorld, events)) →
      events = [accessibilityEvent (ops.selection path) path])

/-- Fail-fast, once-only operation order over every open-dispatch instantiation,
including arbitrary non-Bool values and all failure worlds. Accessibility false
prevents all path calls; non-Bool accessibility raises the documented condition
TypeError; custom errors are not caught again. No correctness law is imposed on
an arbitrary custom method or on a native longpath instantiation.
Julia source: base/loading.jl:13-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:182-193,326-335,790-832. -/
def WindowsCaseSensitiveCorrect : Prop :=
  ∀ (E W P Other Long Left Right : Type)
      (ops : WindowsCaseOps (ObservationM E W) P Other Long Left Right)
      (path : P) (world : W),
    (∀ result finalWorld events,
      observe (isFileCaseSensitiveWindows (E := E) (traceWindows ops) path)
        (world, []) = some (result, (finalWorld, events)) →
      WindowsTrace (ops.accessible.selection path) path events) ∧
    (∀ finalWorld,
      observe (selectedAccessibleFile (E := E) ops.accessible path) world =
        some (.ok (.bool false), finalWorld) →
      observe (isFileCaseSensitiveWindows (E := E) (traceWindows ops) path)
        (world, []) = some (.ok (.bool false),
          (finalWorld, [accessibilityEvent (ops.accessible.selection path) path]))) ∧
    (∀ value finalWorld,
      observe (selectedAccessibleFile (E := E) ops.accessible path) world =
        some (.ok (.other value), finalWorld) →
      observe (isFileCaseSensitiveWindows (E := E) (traceWindows ops) path)
        (world, []) = some (.error .typeError,
          (finalWorld, [accessibilityEvent (ops.accessible.selection path) path]))) ∧
    (∀ error finalWorld,
      observe (selectedAccessibleFile (E := E) ops.accessible path) world =
        some (.error error, finalWorld) →
      observe (isFileCaseSensitiveWindows (E := E) (traceWindows ops) path)
        (world, []) = some (.error error,
          (finalWorld, [accessibilityEvent (ops.accessible.selection path) path]))) ∧
    (observe (selectedAccessibleFile (E := E) ops.accessible path) world = none →
      observe (isFileCaseSensitiveWindows (E := E) (traceWindows ops) path)
        (world, []) = none)


/-- Dynamic trace records preserve native indices and complete Core field errors.
The final `any` event also retains its observed result for transparency checking. -/
inductive GenericEvent (L : Type) where
  | isdir (path : GenericValue L)
  | isfile (path : GenericValue L)
  | ispath (path : GenericValue L)
  | customAccessibleFile (path : GenericValue L)
  | splitdir (path : GenericValue L)
  | indexedFirst (value : GenericValue L) (index : JInt .i64)
  | indexedNext (value : GenericValue L) (index : JInt .i64) (state : GenericValue L)
  | getfield (value index : GenericValue L)
      (result : Except (GenericValue L) (GenericValue L))
  | readdir (dir : GenericValue L)
  | broadcasted (function : BroadcastFunction) (listing filename : GenericValue L)
  | materialize (broadcast : GenericValue L)
  | any (value : GenericValue L)
      (result : Except (DispatchError (GenericValue L)) (DispatchValue (GenericValue L)))

/-- Observe the result of an arbitrary loading action without changing it. -/
def recordResult {E W A Event : Type} (event : Except (DispatchError E) A → Event)
    (action : ObservationM E W A) : ObservationM E (W × List Event) A :=
  ExceptT.mk (StateT.mk (fun initial => do
    let (result, finalWorld) ← observe action initial.1
    pure (result, (finalWorld, initial.2 ++ [event result]))))

/-- The corresponding protected observation of an installed Core action. -/
def recordCoreResult {W L A Event : Type} (event : Except (GenericValue L) A → Event)
    (action : JuliaLean.base.boot.CoreM W L A) :
    JuliaLean.base.boot.CoreM (W × List Event) L A :=
  fun initial => do
    match ← action initial.1 with
    | .ok (value, finalWorld) =>
        pure (.ok (value, (finalWorld, initial.2 ++ [event (.ok value)])))
    | .error (error, finalWorld) =>
        pure (.error (error, (finalWorld, initial.2 ++ [event (.error error)])))

/-- Only Core.int and Core.getfield are reached. The unused fields remain
universally quantified in `otherCore`; no laws or default stubs are supplied.
The two reached fields are bound to the original primitive interface. -/
def traceGeneric {W L : Type} (ops : GenericCaseOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (GenericEvent L)) L) :
    GenericCaseOps (W × List (GenericEvent L)) L where
  core := { otherCore with
    int := ops.core.int
    getfield := fun value index =>
      recordCoreResult (GenericEvent.getfield value index) (ops.core.getfield value index) }
  accessible := {
    predicates := {
      isdir := fun path => record (.isdir path) (ops.accessible.predicates.isdir path)
      isfile := fun path => record (.isfile path) (ops.accessible.predicates.isfile path)
      ispath := fun path => record (.ispath path) (ops.accessible.predicates.ispath path) }
    selection := ops.accessible.selection
    custom := fun path => record (.customAccessibleFile path) (ops.accessible.custom path) }
  splitdir := fun path => record (.splitdir path) (ops.splitdir path)
  indexedIterateFirst := fun value index =>
    record (.indexedFirst value index) (ops.indexedIterateFirst value index)
  indexedIterateNext := fun value index state =>
    record (.indexedNext value index state) (ops.indexedIterateNext value index state)
  readdir := fun dir => record (.readdir dir) (ops.readdir dir)
  broadcasted := fun function listing filename =>
    record (.broadcasted function listing filename) (ops.broadcasted function listing filename)
  materialize := fun broadcast => record (.materialize broadcast) (ops.materialize broadcast)
  any := fun value => recordResult (GenericEvent.any value) (ops.any value)

/-- Stage labels are mathematical observations, not Julia integer arithmetic. -/
def genericStage {L : Type} : GenericEvent L → Nat
  | .isfile _ => 0
  | .customAccessibleFile _ => 0
  | .splitdir _ => 1
  | .indexedFirst _ _ => 2
  | .getfield _ _ _ => 3
  | .indexedNext _ _ _ => 4
  | .readdir _ => 5
  | .broadcasted _ _ _ => 6
  | .materialize _ => 7
  | .any _ _ => 8
  | .isdir _ => 9
  | .ispath _ => 10

/-- The Core adapter preserves termination, all returned values, thrown runtime
values and their final worlds. This registered internal invariant covers the
adapter on every action, not merely successful destructuring.
Julia source: base/loading.jl:79 (destructuring); base/tuple.jl:161-172
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def CoreAdapterCorrect : Prop :=
  ∀ (W L A : Type) (action : JuliaLean.base.boot.CoreM W L A) (world : W),
    (action world = none ↔ observe (liftCoreAction action) world = none) ∧
    (∀ value finalWorld, action world = some (.ok (value, finalWorld)) →
      observe (liftCoreAction action) world = some (.ok value, finalWorld)) ∧
    (∀ error finalWorld, action world = some (.error (error, finalWorld)) →
      observe (liftCoreAction action) world = some (.error (.other error), finalWorld))

/-- The full generic fallback domain, including malformed iteration results and
all Core/dispatch errors: completed traces are nonempty prefixes of the source
stage order, use native indices 1 and 2, forward the first iteration state, and
preserve the final any result/error. Materialization precedes any. All primitive
records and dispatch actions are quantified without correctness assumptions.
Julia source: base/loading.jl:77-81; base/tuple.jl:161-172
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:182-193,326-335;
doc/src/manual/functions.md (destructuring assignment). -/
def GenericCaseSensitiveCorrect : Prop :=
  ∀ (W L : Type) (ops : GenericCaseOps W L)
      (otherCore : JuliaLean.base.boot.CoreOps (W × List (GenericEvent L)) L)
      (path : GenericValue L) (world : W),
    (∀ result finalWorld events,
      observe (isFileCaseSensitiveGeneric (traceGeneric ops otherCore) path)
        (world, []) = some (result, (finalWorld, events)) →
      events ≠ [] ∧
      (∃ suffix, events.map genericStage ++ suffix = [0, 1, 2, 3, 3, 4, 3, 5, 6, 7, 8]) ∧
      (∀ value index, GenericEvent.indexedFirst value index ∈ events → index.val = 1) ∧
      (∀ value index state, GenericEvent.indexedNext value index state ∈ events →
        index.val = 2 ∧ ∃ first,
          GenericEvent.getfield first
            (JuliaLean.base.boot.intV ops.core (JInt.lit .i64 2)) (.ok state) ∈ events) ∧
      (∀ original, GenericEvent.splitdir original ∈ events → original = path) ∧
      (∀ value outcome, events.getLast? = some (.any value outcome) → result = outcome)) ∧
    (∀ finalWorld,
      observe (selectedAccessibleFile (E := GenericValue L) ops.accessible path) world =
        some (.ok (.bool false), finalWorld) →
      observe (isFileCaseSensitiveGeneric ops path) world =
        some (.ok (.bool false), finalWorld)) ∧
    (∀ value finalWorld,
      observe (selectedAccessibleFile (E := GenericValue L) ops.accessible path) world =
        some (.ok (.other value), finalWorld) →
      observe (isFileCaseSensitiveGeneric ops path) world =
        some (.error .typeError, finalWorld)) ∧
    (∀ error finalWorld,
      observe (selectedAccessibleFile (E := GenericValue L) ops.accessible path) world =
        some (.error error, finalWorld) →
      observe (isFileCaseSensitiveGeneric ops path) world = some (.error error, finalWorld)) ∧
    (observe (selectedAccessibleFile (E := GenericValue L) ops.accessible path) world = none →
      observe (isFileCaseSensitiveGeneric ops path) world = none)


inductive DigestEvent (E S Decoded Other : Type) where
  | decode (string : S) (result : Except (DispatchError E) (DigestDecoded S Decoded))
  | construct (kind : DigestKind) (decoded : Decoded)
      (result : Except (DispatchError E) (DigestValue Other))
  | customConstructor (kind : DigestKind) (string : S)
      (result : Except (DispatchError E) (DigestValue Other))
  | customParse (kind : DigestKind) (string : S)
      (result : Except (DispatchError E) (DigestValue Other))

def traceDigestString {E W S Decoded Other : Type}
    (ops : DigestStringOps (ObservationM E W) S Decoded Other) :
    DigestStringOps (ObservationM E (W × List (DigestEvent E S Decoded Other)))
      S Decoded Other where
  hex2bytes := fun string => recordResult (.decode string) (ops.hex2bytes string)
  decodedStringSelection := ops.decodedStringSelection
  constructString := fun kind string =>
    recordResult (.customConstructor kind string) (ops.constructString kind string)
  constructDecoded := fun kind decoded =>
    recordResult (.construct kind decoded) (ops.constructDecoded kind decoded)

def traceDigestConstructor {E W S Decoded Other : Type}
    (ops : DigestConstructorOps (ObservationM E W) S Decoded Other) :
    DigestConstructorOps (ObservationM E (W × List (DigestEvent E S Decoded Other)))
      S Decoded Other where
  stringBody := traceDigestString ops.stringBody
  selection := ops.selection
  custom := fun kind string =>
    recordResult (.customConstructor kind string) (ops.custom kind string)

def traceDigestParse {E W S Decoded Other : Type}
    (ops : DigestParseOps (ObservationM E W) S Decoded Other) :
    DigestParseOps (ObservationM E (W × List (DigestEvent E S Decoded Other)))
      S Decoded Other where
  constructorOps := traceDigestConstructor ops.constructorOps
  selection := ops.selection
  custom := fun kind string => recordResult (.customParse kind string) (ops.custom kind string)

/-- Data/effect-flow invariant on observed events: decoder failure ends the call;
otherwise its actual result selects real Base recursion or one nonrecursive
constructor call of the same digest kind. Terminal outcomes pass through unchanged.
No decoder or constructor law is assumed. -/
inductive DigestConstructionTrace {E S Decoded Other : Type}
    (selection : DigestKind → S → DigestSelection) (kind : DigestKind) :
    S → List (DigestEvent E S Decoded Other) →
      Except (DispatchError E) (DigestValue Other) → Prop where
  | decoderError (string : S) (error : DispatchError E) :
      DigestConstructionTrace selection kind string [.decode string (.error error)] (.error error)
  | finished (string : S) (decoded : Decoded)
      (outcome : Except (DispatchError E) (DigestValue Other)) :
      DigestConstructionTrace selection kind string
        [.decode string (.ok (.other decoded)), .construct kind decoded outcome] outcome
  | customString (string decodedString : S)
      (outcome : Except (DispatchError E) (DigestValue Other)) :
      selection kind decodedString = .custom →
      DigestConstructionTrace selection kind string
        [.decode string (.ok (.string decodedString)),
          .customConstructor kind decodedString outcome] outcome
  | recursive (string nextString : S) (events : List (DigestEvent E S Decoded Other))
      (outcome : Except (DispatchError E) (DigestValue Other)) :
      selection kind nextString = .base →
      DigestConstructionTrace selection kind nextString events outcome →
      DigestConstructionTrace selection kind string
        (.decode string (.ok (.string nextString)) :: events) outcome

/-- Exact selected constructor call, including a genuinely more-specific method. -/
def DigestParseTrace {E S Decoded Other : Type} (selection : DigestSelection)
    (decodedSelection : DigestKind → S → DigestSelection) (kind : DigestKind) (string : S) (events : List (DigestEvent E S Decoded Other))
    (result : Except (DispatchError E) (DigestValue Other)) : Prop :=
  match selection with
  | .base => DigestConstructionTrace decodedSelection kind string events result
  | .custom => events = [.customConstructor kind string result]

/-- Independent class specification for the tryparse catch. -/
def IsArgumentError {E : Type} (error : DispatchError E) : Prop :=
  ∃ value, error = .argumentError value

/-- Total observation relation: the ArgumentError filter preserves final worlds,
all success values, every other error and divergence. -/
def ArgumentFilterInvariant {E W Other : Type}
    (source filtered : Option (Except (DispatchError E) (DigestValue Other) × W)) : Prop :=
  (source = none ↔ filtered = none) ∧
  source.map (fun observation => observation.2) =
    filtered.map (fun observation => observation.2) ∧
  (∀ value finalWorld, source = some (.ok value, finalWorld) →
    filtered = some (.ok value, finalWorld)) ∧
  (∀ error finalWorld, source = some (.error error, finalWorld) →
    (IsArgumentError error → filtered = some (.ok .nothing, finalWorld)) ∧
    (¬ IsArgumentError error → filtered = some (.error error, finalWorld))) ∧
  (∀ error finalWorld, filtered = some (.error error, finalWorld) → ¬ IsArgumentError error)

/-- Both generated AbstractString constructors preserve the actual decoder result
and same SHA type identity through arbitrary Base recursion, and preserve all decoder
errors/effects/divergence. All custom AbstractString/decoded/result carriers and
all callbacks are universally quantified without correctness laws.
Julia source: base/loading.jl:114-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/methods.md (multiple dispatch);
base/strings/util.jl:1217-1237 (hex2bytes). -/
def DigestStringCorrect : Prop :=
  ∀ (E W S Decoded Other : Type)
      (ops : DigestStringOps (ObservationM E W) S Decoded Other)
      (kind : DigestKind) (string : S) (world : W),
    (∀ result finalWorld events,
      observe (digestFromAbstractString (traceDigestString ops) kind string)
        (world, []) = some (result, (finalWorld, events)) →
      DigestConstructionTrace ops.decodedStringSelection kind string events result) ∧
    (∀ error finalWorld, observe (ops.hex2bytes string) world = some (.error error, finalWorld) →
      observe (digestFromAbstractString ops kind string) world = some (.error error, finalWorld)) ∧
    (observe (ops.hex2bytes string) world = none →
      observe (digestFromAbstractString ops kind string) world = none)

/-- Generated parse preserves selected constructor dispatch and its complete return
value. The Base constructor body is exercised rather than replaced by a callback;
a selected custom constructor remains a single uncoerced call.
Julia source: base/loading.jl:114-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/methods.md (multiple dispatch). -/
def ParseDigestCorrect : Prop :=
  ∀ (E W S Decoded Other : Type)
      (ops : DigestConstructorOps (ObservationM E W) S Decoded Other)
      (kind : DigestKind) (string : S) (world : W),
    (∀ result finalWorld events,
      observe (parseDigest (traceDigestConstructor ops) kind string)
        (world, []) = some (result, (finalWorld, events)) →
      DigestParseTrace (ops.selection kind string) ops.stringBody.decodedStringSelection
        kind string events result) ∧
    (ops.selection kind string = .custom →
      observe (parseDigest ops kind string) world = observe (ops.custom kind string) world)

/-- tryparse catches ArgumentError from any selected parse path, retains prior
state effects, returns nothing for that class only, and preserves every other
result/error and divergence. The trace also prevents skipped/repeated dispatch
stages and checks unchanged constructor/type/string arguments.
Julia source: base/loading.jl:114-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:790-832 (selective catch/rethrow). -/
def TryParseDigestCorrect : Prop :=
  ∀ (E W S Decoded Other : Type)
      (ops : DigestParseOps (ObservationM E W) S Decoded Other)
      (kind : DigestKind) (string : S) (world : W),
    ArgumentFilterInvariant (observe (selectedDigestParse ops kind string) world)
      (observe (tryParseDigest (E := E) ops kind string) world) ∧
    (∀ result finalWorld events,
      observe (tryParseDigest (E := E) (traceDigestParse ops) kind string)
        (world, []) = some (result, (finalWorld, events)) →
      ∃ original,
        (match ops.selection kind string with
        | .base => DigestParseTrace (ops.constructorOps.selection kind string)
            ops.constructorOps.stringBody.decodedStringSelection kind string events original
        | .custom => events = [.customParse kind string original]) ∧
        ArgumentFilterInvariant (some (original, finalWorld)) (some (result, finalWorld)))

/-- Instrument the selected call, protecting the argument/reference/outcome log
from arbitrary changes made to the caller's world. -/
def traceParsedTomlDefault {E W S Cache Lock Result : Type}
    (ops : ParsedTomlDefaultOps (ObservationM E W) S Cache Lock Result) :
    ParsedTomlDefaultOps
      (ObservationM E (W × List (S × Cache × Lock × Except (DispatchError E) Result)))
      S Cache Lock Result where
  tomlCache := ops.tomlCache
  requireLock := ops.requireLock
  parsedToml := fun projectFile cache lock =>
    recordResult (fun result => (projectFile, cache, lock, result))
      (ops.parsedToml projectFile cache lock)

/-- Over all AbstractString values and selected callees, the unary wrapper calls
once with its original argument and the exact global cache/lock identities.
Every observed outcome and final world, including failure or divergence, passes
through. No parser/cache correctness assumption is made.
Julia source: base/loading.jl:299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/methods.md (multiple dispatch);
base/loading.jl:297-299 (constant default objects). -/
def ParsedTomlDefaultCorrect : Prop :=
  ∀ (E W S Cache Lock Result : Type)
      (ops : ParsedTomlDefaultOps (ObservationM E W) S Cache Lock Result)
      (projectFile : S) (world : W),
    observe (parsedTomlDefault ops projectFile) world =
      observe (ops.parsedToml projectFile ops.tomlCache ops.requireLock) world ∧
    (∀ result finalWorld events,
      observe (parsedTomlDefault (traceParsedTomlDefault ops) projectFile) (world, []) =
        some (result, (finalWorld, events)) →
      events = [(projectFile, ops.tomlCache, ops.requireLock, result)])


/-- The internal helper's narrow, full-domain contract: nothing is inert; every
other value reaches first exactly once with its identity intact, and retains its
complete observed result. This covers non-iterable inputs and custom first methods
without imposing a correctness law or inventing a package-loading guarantee.
Julia source: base/loading.jl:449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md (conditional evaluation). -/
def NothingOrFirstCorrect : Prop :=
  ∀ (E W A B : Type) (ops : FirstDispatchOps (ObservationM E W) A B) (world : W),
    observe (nothingOrFirst ops none) world = some (.ok none, world) ∧
    (∀ value,
      observe (nothingOrFirst ops (some value)) world = observe (ops.first value) world) ∧
    (∀ input result finalWorld events,
      let traced : FirstDispatchOps
          (ObservationM E (W × List (A × Except (DispatchError E) (Option B)))) A B :=
        { first := fun value => recordResult (fun outcome => (value, outcome)) (ops.first value) }
      observe (nothingOrFirst traced input) (world, []) =
        some (result, (finalWorld, events)) →
      match input with
      | none => events = [] ∧ result = .ok none ∧ finalWorld = world
      | some value => events = [(value, result)])

/-- Protected terminal observations of the package callees. Before/after worlds
make mutation continuity and failure-state preservation independently observable;
open dispatch cannot edit the separate event log.
Julia source: base/loading.jl:767-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:767-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get_here(project_file, name::String)
--     # if `where` matches the project, use [deps] section as manifest, and stop searching
--     pkg_uuid = explicit_project_deps_get(project_file, name)
--     pkg_uuid === nothing && return PkgId(name)
--     return PkgId(pkg_uuid, name)
-- end
-- 
-- function package_get(project_file, where::Union{Nothing, PkgId}, name::String)
--     if where !== nothing
--         proj = project_file_name_uuid(project_file, where.name)
--         proj != where && return nothing
--     end
--     return package_get_here(project_file, name)
-- end
-- /Source
inductive PackageEvent (E W P U Other Proj CompareOther : Type) where
  | dependency (projectFile : P) (name : JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) (Option U)) (after : W)
  | construct (dependency : U) (name : JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) (PackageValue Other)) (after : W)
  | customHere (projectFile : P) (name : JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) (PackageValue Other)) (after : W)
  | identity (projectFile : P) (name : JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) Proj) (after : W)
  | compare (project : Proj) (context : JuliaLean.base.pkgid.PkgId) (before : W)
      (outcome : Except (DispatchError E) (DispatchValue CompareOther)) (after : W)

/-- Observe one arbitrary action and retain its input world, outcome and output
world. This instrumentation changes neither the action nor its error/divergence;
the caller cannot forge records because it receives only W.
Julia source: base/loading.jl:767-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:767-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get_here(project_file, name::String)
--     # if `where` matches the project, use [deps] section as manifest, and stop searching
--     pkg_uuid = explicit_project_deps_get(project_file, name)
--     pkg_uuid === nothing && return PkgId(name)
--     return PkgId(pkg_uuid, name)
-- end
-- 
-- function package_get(project_file, where::Union{Nothing, PkgId}, name::String)
--     if where !== nothing
--         proj = project_file_name_uuid(project_file, where.name)
--         proj != where && return nothing
--     end
--     return package_get_here(project_file, name)
-- end
-- /Source
def recordPackageStep {E W A Event : Type}
    (event : W → Except (DispatchError E) A → W → Event)
    (action : ObservationM E W A) : ObservationM E (W × List Event) A :=
  ExceptT.mk (StateT.mk (fun initial => do
    let (outcome, finalWorld) ← observe action initial.1
    pure (outcome, (finalWorld, initial.2 ++ [event initial.1 outcome finalWorld]))))

/-- Instrument the two independently selected package_get_here callees, retaining
all original arguments and terminal effects. No result law is imposed.
Julia source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get_here(project_file, name::String)
--     # if `where` matches the project, use [deps] section as manifest, and stop searching
--     pkg_uuid = explicit_project_deps_get(project_file, name)
--     pkg_uuid === nothing && return PkgId(name)
--     return PkgId(pkg_uuid, name)
-- end
-- /Source
def tracePackageHere {E W P U Other Proj CompareOther : Type}
    (ops : PackageHereOps (ObservationM E W) P U Other) :
    PackageHereOps
      (ObservationM E (W × List (PackageEvent E W P U Other Proj CompareOther)))
      P U Other where
  explicitProjectDepsGet := fun projectFile name =>
    recordPackageStep (fun before outcome after =>
      .dependency projectFile name before outcome after)
      (ops.explicitProjectDepsGet projectFile name)
  constructPkgId := fun dependency name =>
    recordPackageStep (fun before outcome after =>
      .construct dependency name before outcome after)
      (ops.constructPkgId dependency name)

/-- Retain Base versus custom selection while protecting the observations of
either branch. The Base branch still executes package_get_here itself.
Julia source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get(project_file, where::Union{Nothing, PkgId}, name::String)
--     if where !== nothing
--         proj = project_file_name_uuid(project_file, where.name)
--         proj != where && return nothing
--     end
--     return package_get_here(project_file, name)
-- end
-- /Source
def tracePackageHereDispatch {E W P U Other Proj CompareOther : Type}
    (ops : PackageHereDispatchOps (ObservationM E W) P U Other) :
    PackageHereDispatchOps
      (ObservationM E (W × List (PackageEvent E W P U Other Proj CompareOther)))
      P U Other where
  baseOps := tracePackageHere (Proj := Proj) (CompareOther := CompareOther) ops.baseOps
  selection := ops.selection
  custom := fun projectFile name =>
    recordPackageStep (fun before outcome after =>
      .customHere projectFile name before outcome after)
      (ops.custom projectFile name)

/-- Instrument the identity/comparison guard and the complete selected here path.
The comparison records the exact concrete PkgId and no Boolean coercion.
Julia source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get(project_file, where::Union{Nothing, PkgId}, name::String)
--     if where !== nothing
--         proj = project_file_name_uuid(project_file, where.name)
--         proj != where && return nothing
--     end
--     return package_get_here(project_file, name)
-- end
-- /Source
def tracePackageGet {E W P U Other Proj CompareOther : Type}
    (ops : PackageGetOps (ObservationM E W) P U Other Proj CompareOther) :
    PackageGetOps
      (ObservationM E (W × List (PackageEvent E W P U Other Proj CompareOther)))
      P U Other Proj CompareOther where
  here := tracePackageHereDispatch ops.here
  projectFileNameUuid := fun projectFile name =>
    recordPackageStep (fun before outcome after =>
      .identity projectFile name before outcome after)
      (ops.projectFileNameUuid projectFile name)
  notEqual := fun project context =>
    recordPackageStep (fun before outcome after =>
      .compare project context before outcome after)
      (ops.notEqual project context)

/-- A finite observation language for the here lookup. An absent dependency
produces a native package whose stored UUID is nothing and whose stored bytes
are the requested name, with no further world change. Otherwise the terminal
constructor or custom observation is passed through, including arbitrary errors.
These are independent field, identity and continuity constraints; this relation
does not call the implementation or its installed PkgId constructor.
Julia source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get_here(project_file, name::String)
--     # if `where` matches the project, use [deps] section as manifest, and stop searching
--     pkg_uuid = explicit_project_deps_get(project_file, name)
--     pkg_uuid === nothing && return PkgId(name)
--     return PkgId(pkg_uuid, name)
-- end
-- /Source
def PackageHereTrace {E W P U Other Proj CompareOther : Type}
    (selection : PackageSelection) (projectFile : P) (name : JuliaLean.Strings.JStr)
    (world : W) (result : Except (DispatchError E) (PackageValue Other))
    (finalWorld : W) (events : List (PackageEvent E W P U Other Proj CompareOther)) : Prop :=
  match selection with
  | .custom => events = [.customHere projectFile name world result finalWorld]
  | .base =>
      (∃ error, events = [.dependency projectFile name world (.error error) finalWorld] ∧
        result = .error error) ∨
      (∃ (package : JuliaLean.base.pkgid.PkgId), events = [.dependency projectFile name world (.ok none) finalWorld] ∧
        result = .ok (.pkg package) ∧ package.uuid = none ∧ package.name = name.bytes) ∨
      (∃ dependency nextWorld,
        events = [.dependency projectFile name world (.ok (some dependency)) nextWorld,
          .construct dependency name nextWorld result finalWorld])

/-- Divergence can originate only in a reached open callee: the dependency lookup
or, after a returned non-nothing value, its selected constructor. This liveness
condition assumes no termination or correctness law for either callee.
Julia source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get_here(project_file, name::String)
--     # if `where` matches the project, use [deps] section as manifest, and stop searching
--     pkg_uuid = explicit_project_deps_get(project_file, name)
--     pkg_uuid === nothing && return PkgId(name)
--     return PkgId(pkg_uuid, name)
-- end
-- /Source
def PackageHereDiverges {E W P U Other : Type}
    (ops : PackageHereOps (ObservationM E W) P U Other) (projectFile : P)
    (name : JuliaLean.Strings.JStr) (world : W) : Prop :=
  observe (ops.explicitProjectDepsGet projectFile name) world = none ∨
  ∃ dependency nextWorld,
    observe (ops.explicitProjectDepsGet projectFile name) world =
      some (.ok (some dependency), nextWorld) ∧
    observe (ops.constructPkgId dependency name) nextWorld = none

/-- Full-domain invariant for package_get_here: exactly one lookup preserves the
original project/name, no non-nothing constructor dispatch runs for nothing, the concrete result has
independently specified stored fields, and all subsequent constructor results,
exceptions and worlds pass through. The divergence equivalence excludes a
spuriously nonterminating implementation. The String bound is carried by JStr;
all other values, worlds and effects are universally quantified without laws.
Julia documentation: doc/src/manual/control-flow.md:326-335;
base/pkgid.jl:3-10 (PkgId fields and nothing constructor).
Julia source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:767-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get_here(project_file, name::String)
--     # if `where` matches the project, use [deps] section as manifest, and stop searching
--     pkg_uuid = explicit_project_deps_get(project_file, name)
--     pkg_uuid === nothing && return PkgId(name)
--     return PkgId(pkg_uuid, name)
-- end
-- /Source
def PackageGetHereCorrect : Prop :=
  ∀ (E W P U Other : Type) (ops : PackageHereOps (ObservationM E W) P U Other)
      (projectFile : P) (name : JuliaLean.Strings.JStr) (world : W),
    (∀ result finalWorld events,
      observe (packageGetHere
        (tracePackageHere (Proj := Unit) (CompareOther := Unit) ops) projectFile name)
        (world, []) = some (result, (finalWorld, events)) →
      PackageHereTrace .base projectFile name world result finalWorld events) ∧
    (observe (packageGetHere ops projectFile name) world = none ↔
      PackageHereDiverges ops projectFile name world)

/-- Finite observations of the contextual lookup. No-context runs contain only
the selected here trace. Contextual runs use the stored context name first,
forward that identity result to comparison with the original PkgId, and cannot
reach the here lookup after a failed or rejecting guard. The relation records
all intermediate worlds and terminal outcomes independently of executable code.
Julia source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get(project_file, where::Union{Nothing, PkgId}, name::String)
--     if where !== nothing
--         proj = project_file_name_uuid(project_file, where.name)
--         proj != where && return nothing
--     end
--     return package_get_here(project_file, name)
-- end
-- /Source
def PackageGetTrace {E W P U Other Proj CompareOther : Type}
    (selection : PackageSelection) (projectFile : P) (wherePkg : Option NativePackageId)
    (name : JuliaLean.Strings.JStr) (world : W)
    (result : Except (DispatchError E) (PackageValue Other)) (finalWorld : W)
    (events : List (PackageEvent E W P U Other Proj CompareOther)) : Prop :=
  match wherePkg with
  | none => PackageHereTrace selection projectFile name world result finalWorld events
  | some context =>
      (∃ error,
        events = [.identity projectFile ⟨context.value.name, context.nameSmall⟩
          world (.error error) finalWorld] ∧ result = .error error) ∨
      (∃ project identityWorld compared compareWorld suffix,
        events = [.identity projectFile ⟨context.value.name, context.nameSmall⟩
          world (.ok project) identityWorld,
          .compare project context.value identityWorld compared compareWorld] ++ suffix ∧
        match compared with
        | .error error => suffix = [] ∧ result = .error error ∧ finalWorld = compareWorld
        | .ok (.bool true) =>
            suffix = [] ∧ result = .ok .nothing ∧ finalWorld = compareWorld
        | .ok (.other _) =>
            suffix = [] ∧ result = .error .typeError ∧ finalWorld = compareWorld
        | .ok (.bool false) =>
            PackageHereTrace selection projectFile name compareWorld result finalWorld suffix)

/-- Full-domain contextual package invariant. Terminal observations enforce
once-only source order, original argument identity, the concrete context name,
true/non-Bool guard short-circuiting, and unchanged terminal results, errors and
worlds. Nontermination must originate in a reached callee; no callees are assumed
correct or terminating. Native Strings/PkgIds retain their representation bounds.
The property also covers selectedPackageGetHere through both Base and custom
selection, including the concrete nothing constructor fields.
Julia documentation: doc/src/manual/control-flow.md:182-193,326-335;
base/pkgid.jl:3-10 (stored fields and nothing constructor).
Julia source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function package_get(project_file, where::Union{Nothing, PkgId}, name::String)
--     if where !== nothing
--         proj = project_file_name_uuid(project_file, where.name)
--         proj != where && return nothing
--     end
--     return package_get_here(project_file, name)
-- end
-- /Source
def PackageGetCorrect : Prop :=
  ∀ (E W P U Other Proj CompareOther : Type)
      (ops : PackageGetOps (ObservationM E W) P U Other Proj CompareOther)
      (projectFile : P) (wherePkg : Option NativePackageId)
      (name : JuliaLean.Strings.JStr) (world : W),
    let hereDiverges := fun nextWorld =>
      match ops.here.selection projectFile name with
      | .base => PackageHereDiverges ops.here.baseOps projectFile name nextWorld
      | .custom => observe (ops.here.custom projectFile name) nextWorld = none
    (∀ result finalWorld events,
      observe (packageGet (E := E) (tracePackageGet ops) projectFile wherePkg name)
        (world, []) = some (result, (finalWorld, events)) →
      PackageGetTrace (ops.here.selection projectFile name) projectFile wherePkg name
        world result finalWorld events) ∧
    (observe (packageGet (E := E) ops projectFile wherePkg name) world = none ↔
      match wherePkg with
      | none => hereDiverges world
      | some context =>
          observe (ops.projectFileNameUuid projectFile
            ⟨context.value.name, context.nameSmall⟩) world = none ∨
          ∃ project identityWorld,
            observe (ops.projectFileNameUuid projectFile
              ⟨context.value.name, context.nameSmall⟩) world =
                some (.ok project, identityWorld) ∧
            (observe (ops.notEqual project context.value) identityWorld = none ∨
              ∃ compareWorld,
                observe (ops.notEqual project context.value) identityWorld =
                  some (.ok (.bool false), compareWorld) ∧ hereDiverges compareWorld))

/-- Protected observations of selected base-project and manifest resolution.
Input/output worlds independently expose continuity, including failures.
Julia source: base/loading.jl:981-987. -/
-- Source: base/loading.jl:981-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function workspace_manifest(project_file)
--     base = base_project(project_file)
--     if base !== nothing
--         return project_file_manifest_path(base)
--     end
--     return nothing
-- end
-- /Source
inductive WorkspaceEvent (E W P B R : Type) where
  | baseProject (input : P) (before : W) (outcome : Except (DispatchError E) (Option B)) (after : W)
  | manifest (input : B) (before : W) (outcome : Except (DispatchError E) (Option R)) (after : W)

/-- Instrument the two open dispatch sites without changing their observations.
Julia source: base/loading.jl:981-987. -/
-- Source: base/loading.jl:981-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function workspace_manifest(project_file)
--     base = base_project(project_file)
--     if base !== nothing
--         return project_file_manifest_path(base)
--     end
--     return nothing
-- end
-- /Source
def traceWorkspace {E W P B R : Type}
    (ops : WorkspaceManifestOps (ObservationM E W) P B R) :
    WorkspaceManifestOps (ObservationM E (W × List (WorkspaceEvent E W P B R))) P B R where
  baseProject := fun input => recordPackageStep (.baseProject input) (ops.baseProject input)
  projectFileManifestPath := fun input => recordPackageStep (.manifest input) (ops.projectFileManifestPath input)

/-- Full-domain short-circuit and transparency invariant: nothing stops after
one call, and a non-nothing base is forwarded once unchanged. Protected records
check input/result/state continuity, while the divergence equivalence excludes
spurious nontermination. All open callees are quantified without result laws.
Julia source: base/loading.jl:981-987.
Julia documentation: doc/src/manual/control-flow.md (conditional evaluation). -/
-- Source: base/loading.jl:981-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function workspace_manifest(project_file)
--     base = base_project(project_file)
--     if base !== nothing
--         return project_file_manifest_path(base)
--     end
--     return nothing
-- end
-- /Source
def WorkspaceManifestCorrect : Prop :=
  ∀ (E W P B R : Type) (ops : WorkspaceManifestOps (ObservationM E W) P B R)
      (projectFile : P) (world : W),
    (∀ result finalWorld events,
      observe (workspaceManifest (traceWorkspace ops) projectFile) (world, []) =
        some (result, (finalWorld, events)) →
      ((∃ error,
        events = [.baseProject projectFile world (.error error) finalWorld] ∧
        result = .error error) ∨
       (events = [.baseProject projectFile world (.ok none) finalWorld] ∧ result = .ok none) ∨
       (∃ base nextWorld,
         events = [.baseProject projectFile world (.ok (some base)) nextWorld,
           .manifest base nextWorld result finalWorld]))) ∧
    (observe (workspaceManifest ops projectFile) world = none ↔
      observe (ops.baseProject projectFile) world = none ∨
      ∃ base nextWorld,
        observe (ops.baseProject projectFile) world = some (.ok (some base), nextWorld) ∧
        observe (ops.projectFileManifestPath base) nextWorld = none)

/-- Protected observations of each selected find_source_file call, retaining
its arguments, input world, complete result or exception, and output world.
Selected callees receive W and cannot edit the separate event log.
Julia source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function find_source_file(path::AbstractString)
--     (isabspath(path) || isfile(path)) && return path
--     base_path = joinpath(Sys.BINDIR, DATAROOTDIR, "julia", "base", path)
--     return isfile(base_path) ? normpath(base_path) : nothing
-- end
-- /Source
inductive FindSourceEvent (E W S Joined PredicateOther ResultOther : Type) where
  | isabspath (path : S) (before : W)
      (outcome : Except (DispatchError E) (DispatchValue PredicateOther)) (after : W)
  | isfilePath (path : S) (before : W)
      (outcome : Except (DispatchError E) (DispatchValue PredicateOther)) (after : W)
  | joinpath (bindir datarootdir juliaLiteral baseLiteral : JuliaLean.Strings.JStr)
      (path : S) (before : W) (outcome : Except (DispatchError E) Joined) (after : W)
  | isfileJoined (joined : Joined) (before : W)
      (outcome : Except (DispatchError E) (DispatchValue PredicateOther)) (after : W)
  | normpath (joined : Joined) (before : W)
      (outcome : Except (DispatchError E) (FindSourceValue S ResultOther)) (after : W)

/-- Instrument all five independently selected calls without constraining their
results, mutations, exceptions, or divergence. Native globals and all five
joinpath arguments are retained separately, including the exact original S.
Julia source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def traceFindSource {E W S Joined PredicateOther ResultOther : Type}
    (ops : FindSourceOps (ObservationM E W) S Joined PredicateOther ResultOther) :
    FindSourceOps
      (ObservationM E
        (W × List (FindSourceEvent E W S Joined PredicateOther ResultOther)))
      S Joined PredicateOther ResultOther where
  bindir := ops.bindir
  datarootdir := ops.datarootdir
  isabspath := fun path =>
    recordPackageStep (fun before outcome after => .isabspath path before outcome after)
      (ops.isabspath path)
  isfilePath := fun path =>
    recordPackageStep (fun before outcome after => .isfilePath path before outcome after)
      (ops.isfilePath path)
  joinpath := fun bindir datarootdir juliaLiteral baseLiteral path =>
    recordPackageStep (fun before outcome after =>
      .joinpath bindir datarootdir juliaLiteral baseLiteral path before outcome after)
      (ops.joinpath bindir datarootdir juliaLiteral baseLiteral path)
  isfileJoined := fun joined =>
    recordPackageStep (fun before outcome after => .isfileJoined joined before outcome after)
      (ops.isfileJoined joined)
  normpath := fun joined =>
    recordPackageStep (fun before outcome after => .normpath joined before outcome after)
      (ops.normpath joined)

/-- Independent finite language of completed source observations. Every word
specifies the exact reached calls once, continuous intermediate worlds, original
argument and returned-value identity, and the permitted terminal observation.
The literal constraints state code units directly, without calling the model's
literal definitions. Arbitrary normpath results and all reached errors are
terminal observations, including their mutations. This is a Prop relation on
observations, not an executable expected-result implementation.
Julia source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
inductive FindSourceTrace {E W S Joined PredicateOther ResultOther : Type}
    (bindir datarootdir : JuliaLean.Strings.JStr) (path : S) :
    W → Except (DispatchError E) (FindSourceValue S ResultOther) → W →
      List (FindSourceEvent E W S Joined PredicateOther ResultOther) → Prop where
  | absoluteError (world after : W) (error : DispatchError E) :
      FindSourceTrace bindir datarootdir path world (.error error) after
        [.isabspath path world (.error error) after]
  | absoluteTrue (world after : W) :
      FindSourceTrace bindir datarootdir path world (.ok (.string path)) after
        [.isabspath path world (.ok (.bool true)) after]
  | absoluteNonBool (world after : W) (value : PredicateOther) :
      FindSourceTrace bindir datarootdir path world (.error .typeError) after
        [.isabspath path world (.ok (.other value)) after]
  | pathError (world absoluteWorld after : W) (error : DispatchError E) :
      FindSourceTrace bindir datarootdir path world (.error error) after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.error error) after]
  | pathTrue (world absoluteWorld after : W) :
      FindSourceTrace bindir datarootdir path world (.ok (.string path)) after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.ok (.bool true)) after]
  | pathNonBool (world absoluteWorld after : W) (value : PredicateOther) :
      FindSourceTrace bindir datarootdir path world (.error .typeError) after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.ok (.other value)) after]
  | joinError (world absoluteWorld pathWorld after : W) (error : DispatchError E)
      (juliaLiteral baseLiteral : JuliaLean.Strings.JStr)
      (juliaBytes : juliaLiteral.bytes = [106, 117, 108, 105, 97])
      (baseBytes : baseLiteral.bytes = [98, 97, 115, 101]) :
      FindSourceTrace bindir datarootdir path world (.error error) after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.ok (.bool false)) pathWorld,
          .joinpath bindir datarootdir juliaLiteral baseLiteral path pathWorld
            (.error error) after]
  | joinedError (world absoluteWorld pathWorld joinWorld after : W)
      (joined : Joined) (error : DispatchError E)
      (juliaLiteral baseLiteral : JuliaLean.Strings.JStr)
      (juliaBytes : juliaLiteral.bytes = [106, 117, 108, 105, 97])
      (baseBytes : baseLiteral.bytes = [98, 97, 115, 101]) :
      FindSourceTrace bindir datarootdir path world (.error error) after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.ok (.bool false)) pathWorld,
          .joinpath bindir datarootdir juliaLiteral baseLiteral path pathWorld
            (.ok joined) joinWorld,
          .isfileJoined joined joinWorld (.error error) after]
  | joinedFalse (world absoluteWorld pathWorld joinWorld after : W)
      (joined : Joined) (juliaLiteral baseLiteral : JuliaLean.Strings.JStr)
      (juliaBytes : juliaLiteral.bytes = [106, 117, 108, 105, 97])
      (baseBytes : baseLiteral.bytes = [98, 97, 115, 101]) :
      FindSourceTrace bindir datarootdir path world (.ok .nothing) after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.ok (.bool false)) pathWorld,
          .joinpath bindir datarootdir juliaLiteral baseLiteral path pathWorld
            (.ok joined) joinWorld,
          .isfileJoined joined joinWorld (.ok (.bool false)) after]
  | joinedNonBool (world absoluteWorld pathWorld joinWorld after : W)
      (joined : Joined) (value : PredicateOther)
      (juliaLiteral baseLiteral : JuliaLean.Strings.JStr)
      (juliaBytes : juliaLiteral.bytes = [106, 117, 108, 105, 97])
      (baseBytes : baseLiteral.bytes = [98, 97, 115, 101]) :
      FindSourceTrace bindir datarootdir path world (.error .typeError) after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.ok (.bool false)) pathWorld,
          .joinpath bindir datarootdir juliaLiteral baseLiteral path pathWorld
            (.ok joined) joinWorld,
          .isfileJoined joined joinWorld (.ok (.other value)) after]
  | normalized (world absoluteWorld pathWorld joinWorld foundWorld after : W)
      (joined : Joined) (outcome : Except (DispatchError E) (FindSourceValue S ResultOther))
      (juliaLiteral baseLiteral : JuliaLean.Strings.JStr)
      (juliaBytes : juliaLiteral.bytes = [106, 117, 108, 105, 97])
      (baseBytes : baseLiteral.bytes = [98, 97, 115, 101]) :
      FindSourceTrace bindir datarootdir path world outcome after
        [.isabspath path world (.ok (.bool false)) absoluteWorld,
          .isfilePath path absoluteWorld (.ok (.bool false)) pathWorld,
          .joinpath bindir datarootdir juliaLiteral baseLiteral path pathWorld
            (.ok joined) joinWorld,
          .isfileJoined joined joinWorld (.ok (.bool true)) foundWorld,
          .normpath joined foundWorld outcome after]

/-- The five source call positions, including the exact joined value used by
the final check and normalization. No implementation result is computed here.
Julia source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
inductive FindSourcePoint (Joined : Type) where
  | absolute
  | pathFile
  | joinPath
  | joinedFile (joined : Joined)
  | normalize (joined : Joined)

/-- Source reachability witnesses use only observations of selected callees.
Only false predicates reach the joined-path construction; only a true final
predicate reaches normalization. Failed or non-Bool observations have no next
position. The relation makes no callee-correctness or termination assumption.
Julia source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
inductive FindSourceReachable {E W S Joined PredicateOther ResultOther : Type}
    (ops : FindSourceOps (ObservationM E W) S Joined PredicateOther ResultOther)
    (path : S) (initial : W) : FindSourcePoint Joined → W → Prop where
  | start : FindSourceReachable ops path initial .absolute initial
  | pathFile (after : W)
      (absoluteFalse : observe (ops.isabspath path) initial =
        some (.ok (.bool false), after)) :
      FindSourceReachable ops path initial .pathFile after
  | joinPath (before after : W)
      (reached : FindSourceReachable ops path initial .pathFile before)
      (pathFalse : observe (ops.isfilePath path) before =
        some (.ok (.bool false), after)) :
      FindSourceReachable ops path initial .joinPath after
  | joinedFile (before after : W) (joined : Joined)
      (reached : FindSourceReachable ops path initial .joinPath before)
      (joinedResult : observe (ops.joinpath ops.bindir ops.datarootdir
        findSourceJuliaLiteral findSourceBaseLiteral path) before = some (.ok joined, after)) :
      FindSourceReachable ops path initial (.joinedFile joined) after
  | normalize (before after : W) (joined : Joined)
      (reached : FindSourceReachable ops path initial (.joinedFile joined) before)
      (foundTrue : observe (ops.isfileJoined joined) before =
        some (.ok (.bool true), after)) :
      FindSourceReachable ops path initial (.normalize joined) after

/-- Nontermination requires a diverging selected call at a source-reachable
position, with the exact intermediate argument and world. This relation never
calls findSourceFile and computes no expected successful result.
Julia source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FindSourceDiverges {E W S Joined PredicateOther ResultOther : Type}
    (ops : FindSourceOps (ObservationM E W) S Joined PredicateOther ResultOther)
    (path : S) (world : W) : Prop :=
  ∃ point before,
    FindSourceReachable ops path world point before ∧
    match point with
    | .absolute => observe (ops.isabspath path) before = none
    | .pathFile => observe (ops.isfilePath path) before = none
    | .joinPath => observe (ops.joinpath ops.bindir ops.datarootdir
        findSourceJuliaLiteral findSourceBaseLiteral path) before = none
    | .joinedFile joined => observe (ops.isfileJoined joined) before = none
    | .normalize joined => observe (ops.normpath joined) before = none

/-- Full-domain, law-free find_source_file invariant. Protected traces enforce
source order and once-only calls, exact original and joined value identity,
both native globals and both literal byte sequences, all three Bool checks,
short-circuiting, and terminal value/error/world transparency. Erasing the log
must recover the uninstrumented observation. The reachability equivalence
excludes spurious divergence and excludes termination after a reached diverging
callee. Every carrier, state, selected callee, and effect is universally
quantified; the final normpath observation may be nothing, any S, any other
value, any exception, or divergence.
Julia documentation: doc/src/manual/control-flow.md:180-205,259-272,326-335.
Julia source: base/loading.jl:1346-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FindSourceFileCorrect : Prop :=
  findSourceJuliaLiteral.bytes = [106, 117, 108, 105, 97] ∧
  findSourceBaseLiteral.bytes = [98, 97, 115, 101] ∧
  ∀ (E W S Joined PredicateOther ResultOther : Type)
      (ops : FindSourceOps (ObservationM E W) S Joined PredicateOther ResultOther)
      (path : S) (world : W),
    let traced := observe (findSourceFile (E := E) (traceFindSource ops) path) (world, [])
    let plain := observe (findSourceFile (E := E) ops path) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result finalWorld events,
      traced = some (result, (finalWorld, events)) →
      FindSourceTrace ops.bindir ops.datarootdir path world result finalWorld events) ∧
    (plain = none ↔ FindSourceDiverges ops path world)

/-- Protected observations of the generic index closure and its installed Core
constructor. Raw Core errors retain their values, while dispatch errors retain
the existing tagged classes; every event includes its input and output worlds.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
inductive SortByEvent (W L I : Type) where
  | pkgimages (handle : Nat) (index : I) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)
  | paths (handle : Nat) (index : I) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)
  | mtime (input : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)
  | applyType (head : GenericValue L) (parameters : List (GenericValue L)) (before : W)
      (outcome : Except (GenericValue L) (GenericValue L)) (after : W)
  | splatnew (target arguments : GenericValue L) (before : W)
      (outcome : Except (GenericValue L) (GenericValue L)) (after : W)

/-- Observe a primitive Core action without changing its runtime exception,
result, final world or divergence. The separate log is unavailable to that
action. This is the Core counterpart of recordPackageStep.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def recordSortCoreStep {W L A Event : Type}
    (event : W → Except (GenericValue L) A → W → Event)
    (action : JuliaLean.base.boot.CoreM W L A) :
    JuliaLean.base.boot.CoreM (W × List Event) L A :=
  fun initial => do
    match ← action initial.1 with
    | .ok (value, finalWorld) =>
        pure (.ok (value, (finalWorld,
          initial.2 ++ [event initial.1 (.ok value) finalWorld])))
    | .error (error, finalWorld) =>
        pure (.error (error, (finalWorld,
          initial.2 ++ [event initial.1 (.error error) finalWorld])))

/-- Protect all three selected call observations and the two reached Core
operations. NamedTuple_names uses only tuple, core, typeOf, applyType and
splatnew. The first three remain the original pure representation operations;
the two effectful operations are observed. All unused fields of otherCore remain
universally quantified and are never called.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def traceSortBy {W L I : Type} (ops : SortByOps W L I)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (SortByEvent W L I)) L) :
    SortByOps (W × List (SortByEvent W L I)) L I where
  core := { otherCore with
    tuple := ops.core.tuple
    core := ops.core.core
    typeOf := ops.core.typeOf
    applyType := fun head parameters =>
      recordSortCoreStep (.applyType head parameters) (ops.core.applyType head parameters)
    splatnew := fun target arguments =>
      recordSortCoreStep (.splatnew target arguments) (ops.core.splatnew target arguments) }
  pkgimagesGetindex := fun handle index =>
    recordPackageStep (.pkgimages handle index) (ops.pkgimagesGetindex handle index)
  pathsGetindex := fun handle index =>
    recordPackageStep (.paths handle index) (ops.pathsGetindex handle index)
  mtime := fun input => recordPackageStep (.mtime input) (ops.mtime input)

/-- Independent constructor-argument and outcome constraints: the field names
are exactly pkgimage then mtime, the values retain that order, the actual tuple
type is used, and the primitive outcome/world passes through. No field-access
law is assumed of an arbitrary Core record, and the expected output does not
call NamedTuple_names or sortBy.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortByConstructionTrace {W L I : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (pkgimage modified : GenericValue L) (world : W)
    (result : Except (DispatchError (GenericValue L)) (GenericValue L)) (finalWorld : W)
    (events : List (SortByEvent W L I)) : Prop :=
  let names := JuliaLean.base.boot.tupleV core [.symbol "pkgimage", .symbol "mtime"]
  let values := JuliaLean.base.boot.tupleV core [pkgimage, modified]
  let head := JuliaLean.base.boot.coreV core "NamedTuple"
  let parameters := [names, JuliaLean.base.expr.Value.leaf (core.typeOf values)]
  (∃ error, events = [.applyType head parameters world (.error error) finalWorld] ∧
    result = .error (.other error)) ∨
  (∃ target nextWorld outcome,
    events = [.applyType head parameters world (.ok target) nextWorld,
      .splatnew target values nextWorld outcome finalWorld] ∧
    result = outcome.mapError DispatchError.other)

/-- A fixed-field NamedTuple construction cannot introduce divergence unless
one of its reached primitive operations diverges. Errors are terminating
outcomes, not an artificial lack of progress.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortByConstructionDiverges {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (pkgimage modified : GenericValue L) (world : W) : Prop :=
  let names := JuliaLean.base.boot.tupleV core [.symbol "pkgimage", .symbol "mtime"]
  let values := JuliaLean.base.boot.tupleV core [pkgimage, modified]
  let head := JuliaLean.base.boot.coreV core "NamedTuple"
  let parameters := [names, JuliaLean.base.expr.Value.leaf (core.typeOf values)]
  core.applyType head parameters world = none ∨
  ∃ target nextWorld,
    core.applyType head parameters world = some (.ok (target, nextWorld)) ∧
    core.splatnew target values nextWorld = none

/-- Finite traces retain captured handle identity and the original index at
both reads, then pass the actual path value to mtime. The first failing step
terminates with its unchanged exception/world; successful values reach the
fixed-field constructor in order. No native index or result specialization is
assumed by this observation language.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortByTrace {W L I : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (paths pkgimages : Nat) (index : I) (world : W)
    (result : Except (DispatchError (GenericValue L)) (GenericValue L)) (finalWorld : W)
    (events : List (SortByEvent W L I)) : Prop :=
  (∃ error, events = [.pkgimages pkgimages index world (.error error) finalWorld] ∧
    result = .error error) ∨
  (∃ image imageWorld error,
    events = [.pkgimages pkgimages index world (.ok image) imageWorld,
      .paths paths index imageWorld (.error error) finalWorld] ∧ result = .error error) ∨
  (∃ image imageWorld path pathWorld error,
    events = [.pkgimages pkgimages index world (.ok image) imageWorld,
      .paths paths index imageWorld (.ok path) pathWorld,
      .mtime path pathWorld (.error error) finalWorld] ∧ result = .error error) ∨
  (∃ image imageWorld path pathWorld modified modifiedWorld suffix,
    events = [.pkgimages pkgimages index world (.ok image) imageWorld,
      .paths paths index imageWorld (.ok path) pathWorld,
      .mtime path pathWorld (.ok modified) modifiedWorld] ++ suffix ∧
    SortByConstructionTrace core image modified modifiedWorld result finalWorld suffix)

/-- Every index, selected getindex/mtime action, primitive record and world is
included. The invariant checks source order, original captures/index, both fixed
NamedTuple fields, all terminal outcomes and world continuity. Its divergence
equivalence excludes spontaneous looping and skipped divergent callees. No
correctness law is imposed on dispatch or Core operations.
Julia documentation: doc/src/manual/functions.md:377-393 (named tuple fields);
base/boot.jl:1024-1026 (fixed-name constructor).
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortByCorrect : Prop :=
  ∀ (W L I : Type) (ops : SortByOps W L I)
      (otherCore : JuliaLean.base.boot.CoreOps (W × List (SortByEvent W L I)) L)
      (paths pkgimages : Nat) (index : I) (world : W),
    (∀ result finalWorld events,
      observe (sortBy (traceSortBy ops otherCore) paths pkgimages index) (world, []) =
        some (result, (finalWorld, events)) →
      SortByTrace ops.core paths pkgimages index world result finalWorld events) ∧
    (observe (sortBy ops paths pkgimages index) world = none ↔
      observe (ops.pkgimagesGetindex pkgimages index) world = none ∨
      ∃ image imageWorld,
        observe (ops.pkgimagesGetindex pkgimages index) world = some (.ok image, imageWorld) ∧
        (observe (ops.pathsGetindex paths index) imageWorld = none ∨
          ∃ path pathWorld,
            observe (ops.pathsGetindex paths index) imageWorld = some (.ok path, pathWorld) ∧
            (observe (ops.mtime path) pathWorld = none ∨
              ∃ modified modifiedWorld,
                observe (ops.mtime path) pathWorld = some (.ok modified, modifiedWorld) ∧
                SortByConstructionDiverges ops.core image modified modifiedWorld)))

/-- Protected generic comparator observations. All property reads are separate
events, including the second reads of pkgimage after a true inequality. Their
values can differ because getters and comparison can mutate the world.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
inductive SortLtEvent (E W V Other : Type) where
  | property (input : V) (field : SortProperty) (before : W)
      (outcome : Except (DispatchError E) V) (after : W)
  | different (left right : V) (before : W)
      (outcome : Except (DispatchError E) (DispatchValue Other)) (after : W)
  | less (left right : V) (before : W)
      (outcome : Except (DispatchError E) V) (after : W)

/-- Instrument each selected generic comparator operation independently. The
caller sees only its own world; result/error and before/after worlds are recorded
without assuming that property access or comparison is pure.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def traceSortLt {E W V Other : Type} (ops : SortLtOps (ObservationM E W) V Other) :
    SortLtOps (ObservationM E (W × List (SortLtEvent E W V Other))) V Other where
  getproperty := fun input field =>
    recordPackageStep (.property input field) (ops.getproperty input field)
  notEqual := fun left right =>
    recordPackageStep (.different left right) (ops.notEqual left right)
  lessThan := fun left right =>
    recordPackageStep (.less left right) (ops.lessThan left right)

/-- The comparison branch must freshly read the indicated field on a then b;
less-than receives those fresh results and its entire terminal observation is
returned. An earlier getter failure prevents all later calls.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortLtBranchTrace {E W V Other : Type} (a b : V) (field : SortProperty)
    (world : W) (result : Except (DispatchError E) V) (finalWorld : W)
    (events : List (SortLtEvent E W V Other)) : Prop :=
  (∃ error, events = [.property a field world (.error error) finalWorld] ∧
    result = .error error) ∨
  (∃ left nextWorld error,
    events = [.property a field world (.ok left) nextWorld,
      .property b field nextWorld (.error error) finalWorld] ∧ result = .error error) ∨
  (∃ left leftWorld right rightWorld,
    events = [.property a field world (.ok left) leftWorld,
      .property b field leftWorld (.ok right) rightWorld,
      .less left right rightWorld result finalWorld])

/-- Full finite comparator traces. The first comparison is a Boolean guard;
a non-Bool raises at that guard and no branch getter runs. A true result requires
two new pkgimage reads, whereas false requires the mtime reads. Final less-than
results remain arbitrary values rather than becoming another Boolean guard.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortLtTrace {E W V Other : Type} (a b : V) (world : W)
    (result : Except (DispatchError E) V) (finalWorld : W)
    (events : List (SortLtEvent E W V Other)) : Prop :=
  (∃ error, events = [.property a .pkgimage world (.error error) finalWorld] ∧
    result = .error error) ∨
  (∃ left nextWorld error,
    events = [.property a .pkgimage world (.ok left) nextWorld,
      .property b .pkgimage nextWorld (.error error) finalWorld] ∧ result = .error error) ∨
  (∃ left leftWorld right rightWorld compared comparedWorld suffix,
    events = [.property a .pkgimage world (.ok left) leftWorld,
      .property b .pkgimage leftWorld (.ok right) rightWorld,
      .different left right rightWorld compared comparedWorld] ++ suffix ∧
    match compared with
    | .error error => suffix = [] ∧ result = .error error ∧ finalWorld = comparedWorld
    | .ok (.other _) => suffix = [] ∧ result = .error .typeError ∧ finalWorld = comparedWorld
    | .ok (.bool true) => SortLtBranchTrace a b .pkgimage comparedWorld result finalWorld suffix
    | .ok (.bool false) => SortLtBranchTrace a b .mtime comparedWorld result finalWorld suffix)

/-- A reached comparison branch diverges exactly when one of its two fresh
property reads or its final less-than call diverges; all error outcomes remain
terminating observations.
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortLtBranchDiverges {E W V Other : Type}
    (ops : SortLtOps (ObservationM E W) V Other) (a b : V) (field : SortProperty)
    (world : W) : Prop :=
  observe (ops.getproperty a field) world = none ∨
  ∃ left leftWorld,
    observe (ops.getproperty a field) world = some (.ok left, leftWorld) ∧
    (observe (ops.getproperty b field) leftWorld = none ∨
      ∃ right rightWorld,
        observe (ops.getproperty b field) leftWorld = some (.ok right, rightWorld) ∧
        observe (ops.lessThan left right) rightWorld = none)

/-- Every input and callee is included, including missing properties, arbitrary
non-Bool guard values, mutable getters, exceptions and divergence. Protected
traces verify both repeated reads, the guard-selected property names, argument
forwarding and complete terminal state/result transparency. No result or
correctness law is assumed for getproperty, != or <.
Julia documentation: doc/src/manual/control-flow.md:182-193 (Boolean conditions);
doc/src/manual/interfaces.md (custom property access).
Julia source: base/loading.jl:1403-1409 (captured context 1401-1415)
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/loading.jl:1401-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sort_cachefile_candidates!(paths::Vector{String}, pkgimages::Vector{Bool})
--     length(paths) > 1 || return paths
--     sort_by(i) = (; pkgimage=pkgimages[i], mtime=mtime(paths[i]))
--     function sort_lt(a, b)
--         if a.pkgimage != b.pkgimage
--             return a.pkgimage < b.pkgimage
--         end
--         return a.mtime < b.mtime
--     end
--     # allocating the sort vector is less expensive than using sort!(.. by=sort_by),
--     # which would call the relatively slow mtime multiple times per path
--     p = sortperm(sort_by.(eachindex(paths)), lt=sort_lt, rev=true)
--     permute!(paths, p)
--     return paths
-- end
-- /Source
def SortLtCorrect : Prop :=
  ∀ (E W V Other : Type) (ops : SortLtOps (ObservationM E W) V Other)
      (a b : V) (world : W),
    (∀ result finalWorld events,
      observe (sortLt (E := E) (traceSortLt ops) a b) (world, []) =
        some (result, (finalWorld, events)) →
      SortLtTrace a b world result finalWorld events) ∧
    (observe (sortLt (E := E) ops a b) world = none ↔
      observe (ops.getproperty a .pkgimage) world = none ∨
      ∃ left leftWorld,
        observe (ops.getproperty a .pkgimage) world = some (.ok left, leftWorld) ∧
        (observe (ops.getproperty b .pkgimage) leftWorld = none ∨
          ∃ right rightWorld,
            observe (ops.getproperty b .pkgimage) leftWorld = some (.ok right, rightWorld) ∧
            (observe (ops.notEqual left right) rightWorld = none ∨
              ∃ flag comparedWorld,
                observe (ops.notEqual left right) rightWorld =
                  some (.ok (.bool flag), comparedWorld) ∧
                SortLtBranchDiverges ops a b
                  (if flag then .pkgimage else .mtime) comparedWorld)))

/-- Protected observations of both selected operations, retaining all original
arguments and before/after worlds independently of the executable composition.
Julia source: base/loading.jl:1463. -/
-- Source: base/loading.jl:1463-1463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ocachefile_from_cachefile(cachefile) = string(chopsuffix(cachefile, ".ji"), ".", Libc.Libdl.dlext)
-- /Source
inductive ObjectCacheEvent (E W P Chopped R : Type) where
  | chop (input : P) (suffix : JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) Chopped) (after : W)
  | string (input : Chopped) (separator extension : JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) R) (after : W)

/-- The dispatch implementations cannot forge the protected log.
Julia source: base/loading.jl:1463. -/
-- Source: base/loading.jl:1463-1463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ocachefile_from_cachefile(cachefile) = string(chopsuffix(cachefile, ".ji"), ".", Libc.Libdl.dlext)
-- /Source
def traceObjectCache {E W P Chopped R : Type}
    (ops : ObjectCachefileOps (ObservationM E W) P Chopped R) :
    ObjectCachefileOps (ObservationM E (W × List (ObjectCacheEvent E W P Chopped R))) P Chopped R where
  dlExtension := ops.dlExtension
  chopSuffix := fun input suffix => recordPackageStep (.chop input suffix) (ops.chopSuffix input suffix)
  string := fun input separator extension =>
    recordPackageStep (.string input separator extension) (ops.string input separator extension)

/-- Full-domain order, argument and outcome invariant. Suffix removal is called
once with literal .ji; successful results are forwarded unchanged to string with
literal dot and the exact runtime extension. Terminal errors and worlds are not
changed, and divergence has exactly a reached-callee origin. Literal byte checks
are independent of the model's literal constructors; no callee laws are assumed.
Julia source: base/loading.jl:1463.
Julia documentation: doc/src/manual/functions.md (argument evaluation). -/
-- Source: base/loading.jl:1463-1463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ocachefile_from_cachefile(cachefile) = string(chopsuffix(cachefile, ".ji"), ".", Libc.Libdl.dlext)
-- /Source
def ObjectCachefileCorrect : Prop :=
  ∀ (E W P Chopped R : Type) (ops : ObjectCachefileOps (ObservationM E W) P Chopped R)
      (input : P) (world : W),
    (∀ result finalWorld events,
      observe (ocachefileFromCachefile (traceObjectCache ops) input) (world, []) =
        some (result, (finalWorld, events)) →
      ((∃ (suffix : JuliaLean.Strings.JStr), ∃ error,
        suffix.bytes = [46, 106, 105] ∧
        events = [.chop input suffix world (.error error) finalWorld] ∧ result = .error error) ∨
       (∃ (suffix separator : JuliaLean.Strings.JStr), ∃ chopped nextWorld,
         suffix.bytes = [46, 106, 105] ∧ separator.bytes = [46] ∧
         events = [.chop input suffix world (.ok chopped) nextWorld,
           .string chopped separator ops.dlExtension nextWorld result finalWorld]))) ∧
    (observe (ocachefileFromCachefile ops input) world = none ↔
      observe (ops.chopSuffix input ⟨[46, 106, 105], by decide⟩) world = none ∨
      ∃ chopped nextWorld,
        observe (ops.chopSuffix input ⟨[46, 106, 105], by decide⟩) world = some (.ok chopped, nextWorld) ∧
        observe (ops.string chopped ⟨[46], by decide⟩ ops.dlExtension) nextWorld = none)

/-- Protected observations of the untyped seven-argument dispatch. All six
original carriers, the actual final argument, full exceptions, and before/after
worlds are retained outside the state available to the selected callee.
Julia source: base/loading.jl:1969-1970. -/
-- Source: base/loading.jl:1969-1970 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage) =
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage, nothing)
-- /Source
inductive FlagSixEvent (E W Use Debug Bounds Inline Opt Coverage Result : Type) where
  | seven (usePkgimages : Use) (debugLevel : Debug) (checkBounds : Bounds)
      (inlineValue : Inline) (optLevel : Opt) (coverage : Coverage)
      (path : Option JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) Result) (after : W)

/-- Instrument the independently selected seven-argument constructor without
changing any argument, outcome, mutation, exception, or divergence.
Julia source: base/loading.jl:1969-1970. -/
-- Source: base/loading.jl:1969-1970 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage) =
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage, nothing)
-- /Source
def traceFlagSeven {E W Use Debug Bounds Inline Opt Coverage Result : Type}
    (ops : FlagSevenOps (ObservationM E W) Use Debug Bounds Inline Opt Coverage Result) :
    FlagSevenOps
      (ObservationM E
        (W × List (FlagSixEvent E W Use Debug Bounds Inline Opt Coverage Result)))
      Use Debug Bounds Inline Opt Coverage Result where
  constructSeven := fun usePkgimages debugLevel checkBounds inlineValue optLevel coverage path =>
    recordPackageStep (fun before outcome after =>
      .seven usePkgimages debugLevel checkBounds inlineValue optLevel coverage path
        before outcome after)
      (ops.constructSeven usePkgimages debugLevel checkBounds inlineValue optLevel coverage path)

/-- Full-domain forwarding invariant: exactly one selected call receives the
six original objects followed by nothing; its exact result or error and its
world pass through. Trace erasure preserves the actual observation, and
nontermination occurs exactly when that reached callee does not terminate.
No field-conversion, return-type, effect, or termination law is assumed.
Julia documentation: doc/src/manual/constructors.md:41-72.
Julia source: base/loading.jl:1969-1970. -/
-- Source: base/loading.jl:1969-1970 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage) =
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage, nothing)
-- /Source
def CacheFlagsSixCorrect : Prop :=
  ∀ (E W Use Debug Bounds Inline Opt Coverage Result : Type)
      (ops : FlagSevenOps (ObservationM E W) Use Debug Bounds Inline Opt Coverage Result)
      (usePkgimages : Use) (debugLevel : Debug) (checkBounds : Bounds)
      (inlineValue : Inline) (optLevel : Opt) (coverage : Coverage) (world : W),
    let traced := observe (cacheFlagsSix (traceFlagSeven ops) usePkgimages debugLevel
      checkBounds inlineValue optLevel coverage) (world, [])
    let plain := observe (cacheFlagsSix ops usePkgimages debugLevel checkBounds
      inlineValue optLevel coverage) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result after events, traced = some (result, (after, events)) →
      events = [.seven usePkgimages debugLevel checkBounds inlineValue optLevel coverage
        none world result after]) ∧
    (plain = none ↔ observe (ops.constructSeven usePkgimages debugLevel checkBounds
      inlineValue optLevel coverage none) world = none)

/-- Independent mathematical digit specification for OOICCDDP. The five fields
have one, two, two, one, and two bits respectively; the final equation reconstructs
the original byte from those independently specified digits. No installed
bitwise operation, conversion, or model decoder is used in this relation.
Julia source: base/loading.jl:1955,1972-1976. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def FlagByteDigits (flags : JInt .u8) (fields : FlagByteFields) : Prop :=
  (fields.usePkgimages = true ↔ flags.val % 2 = 1) ∧
  fields.debugLevel.val = (flags.val / 2) % 4 ∧
  fields.checkBounds.val = (flags.val / 8) % 4 ∧
  (fields.inlineValue = true ↔ (flags.val / 32) % 2 = 1) ∧
  fields.optLevel.val = (flags.val / 64) % 4 ∧
  flags.val = (if fields.usePkgimages then 1 else 0) + 2 * fields.debugLevel.val +
    8 * fields.checkBounds.val + (if fields.inlineValue then 32 else 0) +
    64 * fields.optLevel.val

/-- A narrow representation invariant for the native-error embedding used by
the public byte constructor. Every success and entire JlError payload is
preserved, ArgumentError keeps its class, and no surrounding world is changed.
This quantifies observations rather than assuming an adapter-correctness law.
Julia source: base/loading.jl:1971-1978 (native numeric calls). -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def FlagNativeLiftInvariant : Prop :=
  ∀ (E W A : Type) (action : Jl A) (world : W),
    (∀ value, action = .ok value →
      observe (liftFlagNative (m := ObservationM (Sum JlError E) W) (E := E) action)
        world = some (.ok value, world)) ∧
    (∀ message, action = .error (.argumentError message) →
      observe (liftFlagNative (m := ObservationM (Sum JlError E) W) (E := E) action)
        world = some (.error (.argumentError (.inl (.argumentError message))), world)) ∧
    (∀ error, action = .error error → (∀ message, error ≠ .argumentError message) →
      observe (liftFlagNative (m := ObservationM (Sum JlError E) W) (E := E) action)
        world = some (.error (.other (.inl error)), world))

/-- Protected leaf observations for the byte constructors. Converted, Inner,
and Result are arbitrary carriers; no successful conversion or constructor
result is silently forced into Int or CacheFlags. Both dispatch levels and the
outer explicit path keyword have separate events.
Julia source: base/loading.jl:1971-1978,2000-2001. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
inductive FlagByteEvent (E W C Converted Inner Result : Type) where
  | convertCoverage (coverage : C) (before : W)
      (outcome : Except (DispatchError (Sum JlError E)) Converted) (after : W)
  | seven (fields : FlagByteFields) (converted : Converted)
      (path : Option JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError (Sum JlError E)) Inner) (after : W)
  | customSix (fields : FlagByteFields) (converted : Converted) (before : W)
      (outcome : Except (DispatchError (Sum JlError E)) Inner) (after : W)
  | customByte (flags : JInt .u8) (coverage : C) (before : W)
      (outcome : Except (DispatchError (Sum JlError E)) Inner) (after : W)
  | keyword (inner : Inner) (path : Option JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError (Sum JlError E)) Result) (after : W)

/-- Instrument the selected six-argument branch. The Base branch still executes
cacheFlagsSix and records its reached seven-argument call; custom dispatch has
its own event. Argument records are made from the actual received values.
Julia source: base/loading.jl:1969-1970,1977. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def traceFlagSixDispatch {E W C Converted Inner Result : Type}
    (ops : FlagSixDispatchOps (ObservationM (Sum JlError E) W) Converted Inner) :
    FlagSixDispatchOps
      (ObservationM (Sum JlError E)
        (W × List (FlagByteEvent E W C Converted Inner Result))) Converted Inner where
  baseOps := {
    constructSeven := fun usePkgimages debugLevel checkBounds inlineValue optLevel converted path =>
      recordPackageStep (fun before outcome after =>
        .seven ⟨usePkgimages, debugLevel, checkBounds, inlineValue, optLevel⟩ converted
          path before outcome after)
        (ops.baseOps.constructSeven usePkgimages debugLevel checkBounds inlineValue
          optLevel converted path) }
  selection := ops.selection
  custom := fun usePkgimages debugLevel checkBounds inlineValue optLevel converted =>
    recordPackageStep (fun before outcome after =>
      .customSix ⟨usePkgimages, debugLevel, checkBounds, inlineValue, optLevel⟩ converted
        before outcome after)
      (ops.custom usePkgimages debugLevel checkBounds inlineValue optLevel converted)

/-- Instrument the generic Int call and its selected final constructor while
leaving native bit decoding concrete and unchanged.
Julia source: base/loading.jl:1971-1978. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def traceFlagByte {E W C Converted Inner Result : Type}
    (ops : FlagByteOps (ObservationM (Sum JlError E) W) C Converted Inner) :
    FlagByteOps
      (ObservationM (Sum JlError E)
        (W × List (FlagByteEvent E W C Converted Inner Result))) C Converted Inner where
  toInt := fun coverage =>
    recordPackageStep (fun before outcome after => .convertCoverage coverage before outcome after)
      (ops.toInt coverage)
  six := traceFlagSixDispatch (C := C) (Result := Result) ops.six

/-- The terminal selected-constructor language specifies exact native fields,
the unchanged conversion result, nothing for Base forwarding, and full terminal
outcome/world transparency. It computes no expected returned value.
Julia source: base/loading.jl:1969-1970,1977. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def FlagByteSixTrace {E W C Converted Inner Result : Type}
    (selection : FlagByteFields → Converted → FlagSelection)
    (fields : FlagByteFields) (converted : Converted) (world : W)
    (outcome : Except (DispatchError (Sum JlError E)) Inner) (after : W)
    (events : List (FlagByteEvent E W C Converted Inner Result)) : Prop :=
  (selection fields converted = .base ∧
    events = [.seven fields converted none world outcome after]) ∨
  (selection fields converted = .custom ∧
    events = [.customSix fields converted world outcome after])

/-- Finite independent source trace language. The original Integer object is
converted exactly once, before one selected constructor. A failed conversion
prevents construction; otherwise mathematically correct native digits and the
exact arbitrary converted object are forwarded. Intermediate worlds are joined
at the recorded conversion boundary, and terminal outcomes are unchanged.
Julia source: base/loading.jl:1971-1978. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def FlagByteTrace {E W C Converted Inner Result : Type}
    (selection : FlagByteFields → Converted → FlagSelection)
    (flags : JInt .u8) (coverage : C) (world : W)
    (outcome : Except (DispatchError (Sum JlError E)) Inner) (after : W)
    (events : List (FlagByteEvent E W C Converted Inner Result)) : Prop :=
  (∃ error,
    events = [.convertCoverage coverage world (.error error) after] ∧ outcome = .error error) ∨
  ∃ fields converted conversionWorld suffix,
    FlagByteDigits flags fields ∧
    events = [.convertCoverage coverage world (.ok converted) conversionWorld] ++ suffix ∧
    FlagByteSixTrace selection fields converted conversionWorld outcome after suffix

/-- Nontermination witness at a source-reachable open call. Native digits are
specified arithmetically; no decoder or complete constructor computes an
expected result here. All callee observations are unrestricted.
Julia source: base/loading.jl:1971-1978. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def FlagByteDiverges {E W C Converted Inner : Type}
    (ops : FlagByteOps (ObservationM (Sum JlError E) W) C Converted Inner)
    (flags : JInt .u8) (coverage : C) (world : W) : Prop :=
  observe (ops.toInt coverage) world = none ∨
  ∃ fields converted conversionWorld,
    FlagByteDigits flags fields ∧
    observe (ops.toInt coverage) world = some (.ok converted, conversionWorld) ∧
    ((ops.six.selection fields converted = .base ∧
      observe (ops.six.baseOps.constructSeven fields.usePkgimages fields.debugLevel
        fields.checkBounds fields.inlineValue fields.optLevel converted none) conversionWorld = none) ∨
     (ops.six.selection fields converted = .custom ∧
      observe (ops.six.custom fields.usePkgimages fields.debugLevel fields.checkBounds
        fields.inlineValue fields.optLevel converted) conversionWorld = none))

/-- Full Integer-domain byte-constructor invariant, including the omitted
native-zero overload. The native decoder is total and agrees with independent
mathematical digits. Generic conversions and both final dispatch branches are
universally quantified without laws, including arbitrary returned types,
errors, state changes, and divergence. The default uses actual native zero and
the installed typed field constructor; its returned fields, empty path, and
unchanged world are specified independently. The public property also covers
the representation-only native-error adapter by its narrow invariant.
Julia documentation: doc/src/manual/methods.md:885-910;
doc/src/manual/constructors.md:41-72.
Julia source: base/loading.jl:1971-1978. -/
-- Source: base/loading.jl:1971-1978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function CacheFlags(f::UInt8, coverage::Integer=0)
--     use_pkgimages = Bool(f & 1)
--     debug_level = Int((f >> 1) & 3)
--     check_bounds = Int((f >> 3) & 3)
--     inline = Bool((f >> 5) & 1)
--     opt_level = Int((f >> 6) & 3) # define OPT_LEVEL in staticdata_utils
--     CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, Int(coverage))
-- end
-- /Source
def CacheFlagsUInt8Correct : Prop :=
  FlagNativeLiftInvariant ∧
  (∀ flags : JInt .u8, ∃ fields,
    decodeCacheFlagByte flags = .ok fields ∧ FlagByteDigits flags fields) ∧
  (∀ (E W C Converted Result : Type)
      (ops : FlagByteOps (ObservationM (Sum JlError E) W) C Converted Result)
      (flags : JInt .u8) (coverage : C) (world : W),
    let traced := observe
      (cacheFlagsFromUInt8 (E := E) (traceFlagByte (Result := Unit) ops) flags coverage)
      (world, [])
    let plain := observe (cacheFlagsFromUInt8 (E := E) ops flags coverage) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result after events, traced = some (result, (after, events)) →
      FlagByteTrace ops.six.selection flags coverage world result after events) ∧
    (plain = none ↔ FlagByteDiverges ops flags coverage world)) ∧
  (∀ (E W : Type) (flags : JInt .u8) (world : W),
    ∃ cf : JuliaLean.base.loading.CacheFlags,
      observe (cacheFlagsFromUInt8Default
        (m := ObservationM (Sum JlError E) W) (E := E) flags) world = some (.ok cf, world) ∧
      FlagByteDigits flags
        ⟨cf.use_pkgimages, cf.debug_level, cf.check_bounds, cf.inline, cf.opt_level⟩ ∧
      cf.coverage.val = 0 ∧ cf.coverage_path = none)

/-- Retain inner Base/custom selection while protecting the observations of
the real Base body or the selected custom two-argument method.
Julia source: base/loading.jl:2000-2001. -/
-- Source: base/loading.jl:2000-2001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(f::UInt8, coverage::Integer, coverage_path::Union{Nothing,String}) =
--     CacheFlags(CacheFlags(f, coverage); coverage_path)
-- /Source
def traceFlagByteDispatch {E W C Converted Inner Result : Type}
    (ops : FlagByteDispatchOps (ObservationM (Sum JlError E) W) C Converted Inner) :
    FlagByteDispatchOps
      (ObservationM (Sum JlError E)
        (W × List (FlagByteEvent E W C Converted Inner Result))) C Converted Inner where
  baseOps := traceFlagByte (Result := Result) ops.baseOps
  selection := ops.selection
  custom := fun flags coverage =>
    recordPackageStep (fun before outcome after => .customByte flags coverage before outcome after)
      (ops.custom flags coverage)

/-- Instrument the complete inner dispatch and outer keyword call, preserving
arbitrary positional return values and the exact explicit path keyword.
Julia source: base/loading.jl:2000-2001. -/
-- Source: base/loading.jl:2000-2001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(f::UInt8, coverage::Integer, coverage_path::Union{Nothing,String}) =
--     CacheFlags(CacheFlags(f, coverage); coverage_path)
-- /Source
def traceFlagPath {E W C Converted Inner Result : Type}
    (ops : FlagPathOps (ObservationM (Sum JlError E) W) C Converted Inner Result) :
    FlagPathOps
      (ObservationM (Sum JlError E)
        (W × List (FlagByteEvent E W C Converted Inner Result))) C Converted Inner Result where
  inner := traceFlagByteDispatch ops.inner
  keyword := fun inner path =>
    recordPackageStep (fun before outcome after => .keyword inner path before outcome after)
      (ops.keyword inner path)

/-- Finite composition language: a source-faithful Base inner trace or one
custom inner call precedes the outer keyword call. An inner error stops with
its exact exception and world. A successful inner object is the identical outer
positional argument, and the explicit keyword and terminal observation pass
through unchanged. No expected constructor result is computed.
Julia source: base/loading.jl:2000-2001. -/
-- Source: base/loading.jl:2000-2001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(f::UInt8, coverage::Integer, coverage_path::Union{Nothing,String}) =
--     CacheFlags(CacheFlags(f, coverage); coverage_path)
-- /Source
def FlagPathTrace {E W C Converted Inner Result : Type}
    (innerSelection : FlagSelection)
    (sixSelection : FlagByteFields → Converted → FlagSelection)
    (flags : JInt .u8) (coverage : C) (path : Option JuliaLean.Strings.JStr) (world : W)
    (outcome : Except (DispatchError (Sum JlError E)) Result) (after : W)
    (events : List (FlagByteEvent E W C Converted Inner Result)) : Prop :=
  ∃ innerOutcome innerWorld «prefix» suffix,
    events = «prefix» ++ suffix ∧
    ((innerSelection = .base ∧
      FlagByteTrace sixSelection flags coverage world innerOutcome innerWorld «prefix») ∨
     (innerSelection = .custom ∧
      «prefix» = [.customByte flags coverage world innerOutcome innerWorld])) ∧
    match innerOutcome with
    | .error error => suffix = [] ∧ outcome = .error error ∧ after = innerWorld
    | .ok inner => suffix = [.keyword inner path innerWorld outcome after]

/-- A successful inner Base execution reaches the keyword boundary only after
successful coverage conversion and a successful selected constructor. These
are observations of the leaves with independent digit constraints, not a call
to a complete constructor or an expected-value implementation.
Julia source: base/loading.jl:1971-1978,2000-2001. -/
-- Source: base/loading.jl:2000-2001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(f::UInt8, coverage::Integer, coverage_path::Union{Nothing,String}) =
--     CacheFlags(CacheFlags(f, coverage); coverage_path)
-- /Source
def FlagByteProduces {E W C Converted Inner : Type}
    (ops : FlagByteOps (ObservationM (Sum JlError E) W) C Converted Inner)
    (flags : JInt .u8) (coverage : C) (world : W) (inner : Inner) (after : W) : Prop :=
  ∃ fields converted conversionWorld,
    FlagByteDigits flags fields ∧
    observe (ops.toInt coverage) world = some (.ok converted, conversionWorld) ∧
    ((ops.six.selection fields converted = .base ∧
      observe (ops.six.baseOps.constructSeven fields.usePkgimages fields.debugLevel
        fields.checkBounds fields.inlineValue fields.optLevel converted none) conversionWorld =
          some (.ok inner, after)) ∨
     (ops.six.selection fields converted = .custom ∧
      observe (ops.six.custom fields.usePkgimages fields.debugLevel fields.checkBounds
        fields.inlineValue fields.optLevel converted) conversionWorld = some (.ok inner, after)))

/-- Nontermination must originate in the selected inner source execution or
at the outer keyword call after a successful source-reachable inner result.
The relation depends only on leaf observations and source dispatch metadata.
Julia source: base/loading.jl:2000-2001. -/
-- Source: base/loading.jl:2000-2001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(f::UInt8, coverage::Integer, coverage_path::Union{Nothing,String}) =
--     CacheFlags(CacheFlags(f, coverage); coverage_path)
-- /Source
def FlagPathDiverges {E W C Converted Inner Result : Type}
    (ops : FlagPathOps (ObservationM (Sum JlError E) W) C Converted Inner Result)
    (flags : JInt .u8) (coverage : C) (path : Option JuliaLean.Strings.JStr) (world : W) : Prop :=
  (ops.inner.selection flags coverage = .base ∧
    FlagByteDiverges ops.inner.baseOps flags coverage world) ∨
  (ops.inner.selection flags coverage = .custom ∧
    observe (ops.inner.custom flags coverage) world = none) ∨
  ∃ inner innerWorld,
    ((ops.inner.selection flags coverage = .base ∧
      FlagByteProduces ops.inner.baseOps flags coverage world inner innerWorld) ∨
     (ops.inner.selection flags coverage = .custom ∧
      observe (ops.inner.custom flags coverage) world = some (.ok inner, innerWorld))) ∧
    observe (ops.keyword inner path) innerWorld = none

/-- Complete three-argument caller invariant over the full Integer and bounded
String-or-nothing input domains, arbitrary conversion/intermediate/final result
carriers, both inner dispatch branches, all errors, effects, and divergence.
Protected traces enforce once-only source order, exact argument and result
identity, native bit digits on Base selection, and the explicit keyword.
Trace erasure and source-reachable divergence equivalence prevent observation
changes or spurious termination/nontermination. No callee-correctness law is
assumed; the selected Base inner method remains the actual model body.
Julia documentation: doc/src/manual/methods.md:912-915;
doc/src/manual/functions.md:890-896.
Julia source: base/loading.jl:2000-2001. -/
-- Source: base/loading.jl:2000-2001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- CacheFlags(f::UInt8, coverage::Integer, coverage_path::Union{Nothing,String}) =
--     CacheFlags(CacheFlags(f, coverage); coverage_path)
-- /Source
def CacheFlagsUInt8PathCorrect : Prop :=
  ∀ (E W C Converted Inner Result : Type)
      (ops : FlagPathOps (ObservationM (Sum JlError E) W) C Converted Inner Result)
      (flags : JInt .u8) (coverage : C) (path : Option JuliaLean.Strings.JStr) (world : W),
    let traced := observe (cacheFlagsFromUInt8Path (E := E) (traceFlagPath ops)
      flags coverage path) (world, [])
    let plain := observe (cacheFlagsFromUInt8Path (E := E) ops flags coverage path) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result after events, traced = some (result, (after, events)) →
      FlagPathTrace (ops.inner.selection flags coverage) ops.inner.baseOps.six.selection
        flags coverage path world result after events) ∧
    (plain = none ↔ FlagPathDiverges ops flags coverage path world)

/-- Protected request metadata preserves call kind and exact grouping.
This is an observation representation, not a Julia collection.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
inductive LoadingShowRequest where
  | print (arguments : List LoadingShowArgument)
  | showOptionString (value : Option JuliaLean.Strings.JStr)

/-- A completed selected call retains original IO identity, arguments,
input world, arbitrary result or exception, and output world. The selected
callee cannot forge these protected observations.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
structure LoadingShowEvent (E W IO R : Type) where
  io : IO
  request : LoadingShowRequest
  before : W
  outcome : Except (DispatchError E) (Option R)
  after : W

/-- Instrument the selected leaves without imposing result, error or
state laws. The outer protected log records completed failures as well as
successes; divergence has no completed terminal observation.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def traceLoadingShow {E W IO R : Type}
    (ops : LoadingGenericShowOps (ObservationM E W) IO R) :
    LoadingGenericShowOps
      (ObservationM E (W × List (LoadingShowEvent E W IO R))) IO R where
  print := fun io arguments =>
    recordPackageStep
      (fun before outcome after => ⟨io, .print arguments, before, outcome, after⟩)
      (ops.print io arguments)
  showOptionString := fun io value =>
    recordPackageStep
      (fun before outcome after => ⟨io, .showOptionString value, before, outcome, after⟩)
      (ops.showOptionString io value)

/-- Independent argument observations expose literal code units and
stored field values without invoking the executable model's constructors or
native predicates. These lists are finite specification metadata.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
inductive LoadingShowArgumentSpec where
  | string (bytes : List UInt8)
  | boolean (value : Bool)
  | int64 (value : JInt .i64)
  | int32 (value : JInt .i32)

/-- Expose native String code units, retaining all other argument types
and values. This is only an observation projection.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def loadingShowArgumentView : LoadingShowArgument → LoadingShowArgumentSpec
  | .string value => .string value.bytes
  | .boolean value => .boolean value
  | .int64 value => .int64 value
  | .int32 value => .int32 value

/-- A required observation identifies a whole print argument tuple or
the separately dispatched show call.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
inductive LoadingShowRequestSpec where
  | print (arguments : List LoadingShowArgumentSpec)
  | showOptionString (value : Option (List UInt8))

/-- An observation satisfies its slot only with the same call kind,
arity, argument order, code units and typed scalar values.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def LoadingShowRequestMatches (request : LoadingShowRequest)
    (required : LoadingShowRequestSpec) : Prop :=
  match request, required with
  | .print arguments, .print expected =>
      arguments.map loadingShowArgumentView = expected
  | .showOptionString value, .showOptionString expected =>
      value.map (fun s => s.bytes) = expected
  | _, _ => False

/-- Successful prefixes require every earlier call to have succeeded,
with original IO identity and continuous before/after worlds. This is an
inductive relation on completed observations, not an executable model or a
correctness law for any selected callee.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
inductive LoadingShowPrefix {E W IO R : Type} (io : IO) :
    List LoadingShowRequestSpec → W → W → List (LoadingShowEvent E W IO R) → Prop where
  | empty (world : W) :
      LoadingShowPrefix (E := E) (R := R) io [] world world []
  | step (required : LoadingShowRequestSpec) (request : LoadingShowRequest)
      (rest : List LoadingShowRequestSpec) (before middle after : W)
      (value : Option R) (events : List (LoadingShowEvent E W IO R))
      («matches» : LoadingShowRequestMatches request required)
      (following : LoadingShowPrefix io rest middle after events) :
      LoadingShowPrefix io (required :: rest) before after
        (⟨io, request, before, .ok value, middle⟩ :: events)

/-- Terminal outcomes either stop exactly at the first failing call or
complete every required call once. Errors and final worlds pass through; a
success returns the last print value precisely when the source forwards it,
and otherwise returns actual nothing. This declarative trace language makes
no assumption about how any printer formats, mutates, fails or returns.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def LoadingShowTerminal {E W IO R : Type} (io : IO)
    (required : List LoadingShowRequestSpec) (forwardLast : Bool)
    (world : W) (result : Except (DispatchError E) (Option R)) (finalWorld : W)
    (events : List (LoadingShowEvent E W IO R)) : Prop :=
  (∃ («prefix» : List LoadingShowRequestSpec) (next : LoadingShowRequestSpec)
      (suffix : List LoadingShowRequestSpec) (request : LoadingShowRequest)
      (middle : W) (error : DispatchError E)
      (previous : List (LoadingShowEvent E W IO R)),
    required = «prefix» ++ (next :: suffix) ∧
    LoadingShowPrefix io «prefix» world middle previous ∧
    LoadingShowRequestMatches request next ∧
    events = previous ++ [⟨io, request, middle, .error error, finalWorld⟩] ∧
    result = .error error) ∨
  (∃ («prefix» : List LoadingShowRequestSpec) (last : LoadingShowRequestSpec)
      (request : LoadingShowRequest) (middle : W) (value : Option R)
      (previous : List (LoadingShowEvent E W IO R)),
    required = «prefix» ++ [last] ∧
    LoadingShowPrefix io «prefix» world middle previous ∧
    LoadingShowRequestMatches request last ∧
    events = previous ++ [⟨io, request, middle, .ok value, finalWorld⟩] ∧
    result = .ok (if forwardLast then value else none))

/-- Observe exactly one selected operation when defining reachability.
This does not execute a source method or assume any callee law.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def loadingShowRequestAction {E W IO R : Type}
    (ops : LoadingGenericShowOps (ObservationM E W) IO R) (io : IO)
    (request : LoadingShowRequest) : ObservationM E W (Option R) :=
  match request with
  | .print arguments => ops.print io arguments
  | .showOptionString value => ops.showOptionString io value

/-- A required call is reachable only after the earlier selected calls
actually succeeded in the preceding worlds. Intermediate arbitrary returns
are deliberately unrestricted. This is a Prop witness, not an expected-result
implementation and not a callee-correctness premise.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
inductive LoadingShowReachedPrefix {E W IO R : Type}
    (ops : LoadingGenericShowOps (ObservationM E W) IO R) (io : IO) :
    List LoadingShowRequestSpec → W → W → Prop where
  | empty (world : W) : LoadingShowReachedPrefix ops io [] world world
  | step (required : LoadingShowRequestSpec) (request : LoadingShowRequest)
      (rest : List LoadingShowRequestSpec) (before middle after : W) (value : Option R)
      («matches» : LoadingShowRequestMatches request required)
      (observed : observe (loadingShowRequestAction ops io request) before =
        some (.ok value, middle))
      (following : LoadingShowReachedPrefix ops io rest middle after) :
      LoadingShowReachedPrefix ops io (required :: rest) before after

/-- Divergence must originate in a reached selected call after a
successful prefix; an earlier failure prevents later calls from being reached.
The quantified dispatch implementations remain completely arbitrary.
Julia source: base/loading.jl:2104-2124,2186-2201. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def LoadingShowDivergence {E W IO R : Type}
    (ops : LoadingGenericShowOps (ObservationM E W) IO R) (io : IO)
    (required : List LoadingShowRequestSpec) (world : W) : Prop :=
  ∃ («prefix» : List LoadingShowRequestSpec) (next : LoadingShowRequestSpec)
      (suffix : List LoadingShowRequestSpec) (request : LoadingShowRequest) (middle : W),
    required = «prefix» ++ (next :: suffix) ∧
    LoadingShowReachedPrefix ops io «prefix» world middle ∧
    LoadingShowRequestMatches request next ∧
    observe (loadingShowRequestAction ops io request) middle = none

/-- The independent required sequence uses literal code units and the
stored fields directly. The path slot is selected mathematically from the
native coverage value, independently of the model's integer equality call.
Julia source: base/loading.jl:2104-2124. -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
def cacheFlagShowRequirements (cf : JuliaLean.base.loading.CacheFlags) :
    List LoadingShowRequestSpec :=
  [.print [.string [67, 97, 99, 104, 101, 70, 108, 97, 103, 115, 40]],
   .print [.string [59, 32, 117, 115, 101, 95, 112, 107, 103, 105, 109, 97, 103, 101, 115, 61]],
   .print [.boolean cf.use_pkgimages],
   .print [.string [44, 32, 100, 101, 98, 117, 103, 95, 108, 101, 118, 101, 108, 61]],
   .print [.int64 cf.debug_level],
   .print [.string [44, 32, 99, 104, 101, 99, 107, 95, 98, 111, 117, 110, 100, 115, 61]],
   .print [.int64 cf.check_bounds],
   .print [.string [44, 32, 105, 110, 108, 105, 110, 101, 61]],
   .print [.boolean cf.inline],
   .print [.string [44, 32, 111, 112, 116, 95, 108, 101, 118, 101, 108, 61]],
   .print [.int64 cf.opt_level],
   .print [.string [44, 32, 99, 111, 118, 101, 114, 97, 103, 101, 61]],
   .print [.int64 cf.coverage]] ++
  (if cf.coverage.val = 0 then [] else
    [.print [.string [44, 32, 99, 111, 118, 101, 114, 97, 103, 101, 95, 112, 97, 116, 104, 61]],
     .showOptionString cf.coverage_path]) ++
  [.print [.string [41]]]

/-- Full-domain protocol invariant for CacheFlags show. Every selected
operation is quantified without correctness laws. Protected observations
check literal bytes, typed fields, unary grouping, IO identity, fail-fast
ordering, mutations and terminal return. The closing print result passes
through unchanged, and divergence is equivalent to a reached divergent leaf.
The bounded String wrapper is the sole native representation invariant.
Julia source: base/loading.jl:2104-2124.
Julia documentation: doc/src/manual/functions.md (return values);
doc/src/manual/control-flow.md (conditional evaluation and exceptions). -/
-- Source: base/loading.jl:2104-2124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, cf::CacheFlags)
--     print(io, "CacheFlags(")
--     print(io, "; use_pkgimages=")
--     print(io, cf.use_pkgimages)
--     print(io, ", debug_level=")
--     print(io, cf.debug_level)
--     print(io, ", check_bounds=")
--     print(io, cf.check_bounds)
--     print(io, ", inline=")
--     print(io, cf.inline)
--     print(io, ", opt_level=")
--     print(io, cf.opt_level)
--     print(io, ", coverage=")
--     print(io, cf.coverage)
--     # explicit, as evaluating the output would otherwise take the current process's path
--     if cf.coverage != 0
--         print(io, ", coverage_path=")
--         show(io, cf.coverage_path)
--     end
--     print(io, ")")
-- end
-- /Source
def ShowCacheFlagsCorrect : Prop :=
  ∀ (E W IO R : Type) (ops : LoadingGenericShowOps (ObservationM E W) IO R)
      (io : IO) (cf : ShowCacheFlagsNative) (world : W),
    (observe (showCacheFlags ops io cf) world =
      (observe (showCacheFlags (traceLoadingShow ops) io cf) (world, [])).map
        (fun observation => (observation.1, observation.2.1))) ∧
    (∀ result finalWorld events,
      observe (showCacheFlags (traceLoadingShow ops) io cf) (world, []) =
        some (result, (finalWorld, events)) →
      LoadingShowTerminal io (cacheFlagShowRequirements cf.raw) true
        world result finalWorld events) ∧
    (observe (showCacheFlags ops io cf) world = none ↔
      LoadingShowDivergence ops io (cacheFlagShowRequirements cf.raw) world)

/-- The required grouped call sequence is specified from stored bytes
and the mathematical native base value, independently of installed isempty
and integer promotion. Binary and ternary calls remain single observations.
Julia source: base/loading.jl:2186-2201. -/
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def imageTargetShowRequirements (target : JuliaLean.base.loading.ImageTarget) :
    List LoadingShowRequestSpec :=
  [.print [.string target.name]] ++
  (if target.ext_features = [] then [] else
    [.print [.string [44], .string target.ext_features]]) ++
  (if 0 ≤ target.base.val then
    [.print [.string [59, 32, 98, 97, 115, 101, 61], .int32 target.base]] else []) ++
  [.print [.string [59, 32, 102, 108, 97, 103, 115, 61], .int32 target.flags]] ++
  (if target.features_en = [] then [] else
    [.print [.string [59, 32, 102, 101, 97, 116, 117, 114, 101, 115, 95, 101, 110, 61, 40], .string target.features_en, .string [41]]]) ++
  (if target.features_dis = [] then [] else
    [.print [.string [59, 32, 102, 101, 97, 116, 117, 114, 101, 115, 95, 100, 105, 115, 61, 40], .string target.features_dis, .string [41]]])

/-- Full-domain protocol invariant for ImageTarget show, quantified
over arbitrary IO dispatch and every installed native String runtime. The
required trace checks exact grouping, literals, fields, IO identity and
continuous mutation worlds. All reached failures pass through. Empty disabled
features force actual nothing; otherwise the final grouped print result is
returned unchanged. Divergence has exactly a reached-callee origin.
Julia source: base/loading.jl:2186-2201.
Julia documentation: doc/src/manual/functions.md (return values);
doc/src/manual/control-flow.md (if expressions return nothing without a branch). -/
-- Source: base/loading.jl:2186-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, it::ImageTarget)
--     print(io, it.name)
--     if !isempty(it.ext_features)
--         print(io, ",", it.ext_features)
--     end
--     if it.base >= 0
--         print(io, "; base=", it.base)
--     end
--     print(io, "; flags=", it.flags)
--     if !isempty(it.features_en)
--         print(io, "; features_en=(", it.features_en, ")")
--     end
--     if !isempty(it.features_dis)
--         print(io, "; features_dis=(", it.features_dis, ")")
--     end
-- end
-- /Source
def ShowImageTargetCorrect : Prop :=
  ∀ (E W IO R : Type) (rt : JuliaLean.base.strings.search.StringRuntime)
      (ops : LoadingGenericShowOps (ObservationM E W) IO R)
      (io : IO) (target : ShowImageTargetNative) (world : W),
    (observe (showImageTarget rt ops io target) world =
      (observe (showImageTarget rt (traceLoadingShow ops) io target) (world, [])).map
        (fun observation => (observation.1, observation.2.1))) ∧
    (∀ result finalWorld events,
      observe (showImageTarget rt (traceLoadingShow ops) io target) (world, []) =
        some (result, (finalWorld, events)) →
      LoadingShowTerminal io (imageTargetShowRequirements target.raw)
        (decide (target.raw.features_dis ≠ [])) world result finalWorld events) ∧
    (observe (showImageTarget rt ops io target) world = none ↔
      LoadingShowDivergence ops io (imageTargetShowRequirements target.raw) world)


/-- Protected observations of the native Ref read and the selected internal
methods. Both carriers retain exact exception values and before/after worlds.
The selected action cannot access or forge this separate event list.
Julia source: base/loading.jl:2677-2680. -/
-- Source: base/loading.jl:2677-2680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _include_dependency(mod::Module, _path::AbstractString; track_content::Bool=true,
--                              path_may_be_dir::Bool=false)
--     _include_dependency!(_require_dependencies, _track_dependencies[], mod, _path, track_content, path_may_be_dir)
-- end
-- /Source
inductive DependencyWrapperEvent (W L Mod Path : Type) where
  | readTrack (reference field : GenericValue L) (before : W)
      (outcome : Except (GenericValue L) (GenericValue L)) (after : W)
  | recordDependency (dependencies tracking : GenericValue L) (module : Mod) (path : Path)
      (trackContent pathMayBeDir : Bool) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)
  | customInternal (module : Mod) (path : Path) (trackContent pathMayBeDir : Bool) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)

/-- Observe the installed getfield primitive and open recorder call without
changing their behavior. Only getfield and the pure nothing representation are
used from Core; every unused field of otherCore remains arbitrary.
Julia source: base/loading.jl:2677-2680. -/
-- Source: base/loading.jl:2677-2680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _include_dependency(mod::Module, _path::AbstractString; track_content::Bool=true,
--                              path_may_be_dir::Bool=false)
--     _include_dependency!(_require_dependencies, _track_dependencies[], mod, _path, track_content, path_may_be_dir)
-- end
-- /Source
def traceDependencyWrapper {W L Mod Path : Type}
    (ops : DependencyWrapperOps W L Mod Path)
    (otherCore : JuliaLean.base.boot.CoreOps
      (W × List (DependencyWrapperEvent W L Mod Path)) L) :
    DependencyWrapperOps (W × List (DependencyWrapperEvent W L Mod Path)) L Mod Path where
  core := { otherCore with
    toLeafOps := ops.core.toLeafOps
    getfield := fun reference field =>
      recordSortCoreStep (.readTrack reference field) (ops.core.getfield reference field) }
  requireDependencies := ops.requireDependencies
  trackDependenciesRef := ops.trackDependenciesRef
  selectedRecord := fun dependencies tracking module path content directory =>
    recordPackageStep (.recordDependency dependencies tracking module path content directory)
      (ops.selectedRecord dependencies tracking module path content directory)

/-- An independent two-call protocol: read exactly field x of the captured
Ref, then forward the actual value along with both captures and all original
arguments. A failed Ref read prevents delegation; any delegated terminal
observation is returned unchanged.
Julia source: base/loading.jl:2677-2680. -/
-- Source: base/loading.jl:2677-2680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _include_dependency(mod::Module, _path::AbstractString; track_content::Bool=true,
--                              path_may_be_dir::Bool=false)
--     _include_dependency!(_require_dependencies, _track_dependencies[], mod, _path, track_content, path_may_be_dir)
-- end
-- /Source
def DependencyWrapperTrace {W L Mod Path : Type}
    (reference dependencies : GenericValue L) (module : Mod) (path : Path)
    (content directory : Bool) (world : W)
    (result : Except (DispatchError (GenericValue L)) (GenericValue L)) (finalWorld : W)
    (events : List (DependencyWrapperEvent W L Mod Path)) : Prop :=
  (∃ error,
    events = [.readTrack reference (.symbol "x") world (.error error) finalWorld] ∧
    result = .error (.other error)) ∨
  (∃ tracking nextWorld,
    events = [.readTrack reference (.symbol "x") world (.ok tracking) nextWorld,
      .recordDependency dependencies tracking module path content directory nextWorld result finalWorld])

/-- Divergence must originate in the reached Ref primitive or the selected
recorder after a successful read. Ordinary errors are terminating outcomes.
Julia source: base/loading.jl:2677-2680. -/
-- Source: base/loading.jl:2677-2680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _include_dependency(mod::Module, _path::AbstractString; track_content::Bool=true,
--                              path_may_be_dir::Bool=false)
--     _include_dependency!(_require_dependencies, _track_dependencies[], mod, _path, track_content, path_may_be_dir)
-- end
-- /Source
def DependencyWrapperDiverges {W L Mod Path : Type}
    (ops : DependencyWrapperOps W L Mod Path) (module : Mod) (path : Path)
    (content directory : Bool) (world : W) : Prop :=
  ops.core.getfield ops.trackDependenciesRef (.symbol "x") world = none ∨
  ∃ tracking nextWorld,
    ops.core.getfield ops.trackDependenciesRef (.symbol "x") world =
      some (.ok (tracking, nextWorld)) ∧
    observe (ops.selectedRecord ops.requireDependencies tracking module path content directory)
      nextWorld = none

/-- Full-domain Ref/delegation invariant with no callee laws. It checks
identity, exact field selector, original arguments, keyword values, first-failure
behavior and complete terminal state/result transparency. The default-call
clause independently checks true/false defaults, and the liveness clause rules
out spontaneous divergence and skipped divergent actions.
Julia source: base/loading.jl:2677-2680. -/
-- Source: base/loading.jl:2677-2680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _include_dependency(mod::Module, _path::AbstractString; track_content::Bool=true,
--                              path_may_be_dir::Bool=false)
--     _include_dependency!(_require_dependencies, _track_dependencies[], mod, _path, track_content, path_may_be_dir)
-- end
-- /Source
def IncludeDependencyInternalCorrect : Prop :=
  ∀ (W L Mod Path : Type) (ops : DependencyWrapperOps W L Mod Path)
      (otherCore : JuliaLean.base.boot.CoreOps
        (W × List (DependencyWrapperEvent W L Mod Path)) L)
      (module : Mod) (path : Path) (content directory : Bool) (world : W),
    (∀ result finalWorld events,
      observe (includeDependencyInternal (traceDependencyWrapper ops otherCore)
        module path content directory) (world, []) = some (result, (finalWorld, events)) →
      DependencyWrapperTrace ops.trackDependenciesRef ops.requireDependencies module path
        content directory world result finalWorld events) ∧
    (observe (includeDependencyInternal ops module path content directory) world = none ↔
      DependencyWrapperDiverges ops module path content directory world) ∧
    (∀ result finalWorld events,
      observe (includeDependencyInternal (traceDependencyWrapper ops otherCore) module path)
        (world, []) = some (result, (finalWorld, events)) →
      DependencyWrapperTrace ops.trackDependenciesRef ops.requireDependencies module path
        true false world result finalWorld events)

/-- The binding-query observations retain the real module value, fixed
symbol, native definedness result, exact exceptions, and world continuity.
The actual installed root traversal is observed independently as a callee.
Julia source: base/loading.jl:2758-2762. -/
-- Source: base/loading.jl:2758-2762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_mapexprs(mod::Module)
--     root = moduleroot(mod)
--     isdefined(root, _include_mapexprs_name) || return nothing
--     return getglobal(root, _include_mapexprs_name)::IncludeMapexprs
-- end
-- /Source
inductive ModuleQueryEvent (W L : Type) where
  | defined (module : GenericValue L) (name : String) (before : W)
      (outcome : Except JuliaLean.base.io.Error Bool) (after : W)
  | readGlobal (module field : GenericValue L) (before : W)
      (outcome : Except (GenericValue L) (GenericValue L)) (after : W)

/-- Carry an installed runtime action through an additional protected log
without changing the log. Original errors, successes, worlds and divergence
are preserved; this permits the real moduleroot loop to run unchanged.
Julia source: base/loading.jl:2758-2762. -/
-- Source: base/loading.jl:2758-2762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_mapexprs(mod::Module)
--     root = moduleroot(mod)
--     isdefined(root, _include_mapexprs_name) || return nothing
--     return getglobal(root, _include_mapexprs_name)::IncludeMapexprs
-- end
-- /Source
def keepModuleQueryLog {W A Event : Type} (action : JuliaLean.base.io.M W A) :
    JuliaLean.base.io.M (W × List Event) A :=
  fun initial => do
    match ← action initial.1 with
    | .ok (value, finalWorld) => pure (.ok (value, (finalWorld, initial.2)))
    | .error (error, finalWorld) => pure (.error (error, (finalWorld, initial.2)))

/-- Protect one native runtime observation while retaining its raw io.Error
payload and failure world. This is a carrier adapter, not a module primitive
or an implementation of isdefined.
Julia source: base/loading.jl:2758-2762. -/
-- Source: base/loading.jl:2758-2762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_mapexprs(mod::Module)
--     root = moduleroot(mod)
--     isdefined(root, _include_mapexprs_name) || return nothing
--     return getglobal(root, _include_mapexprs_name)::IncludeMapexprs
-- end
-- /Source
def recordModuleQueryRuntime {W A Event : Type}
    (event : W → Except JuliaLean.base.io.Error A → W → Event)
    (action : JuliaLean.base.io.M W A) : JuliaLean.base.io.M (W × List Event) A :=
  fun initial => do
    match ← action initial.1 with
    | .ok (value, finalWorld) =>
        pure (.ok (value, (finalWorld,
          initial.2 ++ [event initial.1 (.ok value) finalWorld])))
    | .error (error, finalWorld) =>
        pure (.error (error, (finalWorld,
          initial.2 ++ [event initial.1 (.error error) finalWorld])))

/-- Lift all installed root primitives over the protected log, and record
the separately reached definedness/global read. Core typeassert retains its
original isa, TypeError object and String representations. Unused fields of
the supplied records are arbitrary and cannot affect this method.
Julia source: base/loading.jl:2758-2762. -/
-- Source: base/loading.jl:2758-2762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_mapexprs(mod::Module)
--     root = moduleroot(mod)
--     isdefined(root, _include_mapexprs_name) || return nothing
--     return getglobal(root, _include_mapexprs_name)::IncludeMapexprs
-- end
-- /Source
def traceModuleQuery {W L Mod D N P : Type}
    (ops : IncludeMapexprsQueryOps W L Mod D N P)
    (otherTypes : JuliaLean.base.runtime_internals.TypeOps
      (W × List (ModuleQueryEvent W L)) (GenericValue L) D N Mod P String)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (ModuleQueryEvent W L)) L) :
    IncludeMapexprsQueryOps (W × List (ModuleQueryEvent W L)) L Mod D N P where
  modules := {
    parent := fun module => keepModuleQueryLog (ops.modules.parent module)
    egal := ops.modules.egal
    main := ops.modules.main
    base := ops.modules.base
    core := ops.modules.core
    compiler := ops.modules.compiler
    definedMainBase := keepModuleQueryLog ops.modules.definedMainBase
    getMainBase := keepModuleQueryLog ops.modules.getMainBase
    nameof := fun module => keepModuleQueryLog (ops.modules.nameof module) }
  types := { otherTypes with
    isdefined := fun module name =>
      recordModuleQueryRuntime (.defined module name) (ops.types.isdefined module name) }
  core := { otherCore with
    isa := ops.core.isa
    obj := ops.core.obj
    str := ops.core.str
    toLeafOps := ops.core.toLeafOps
    getglobal := fun module field =>
      recordSortCoreStep (.readGlobal module field) (ops.core.getglobal module field) }
  moduleValue := ops.moduleValue
  tableType := ops.tableType

/-- The post-root binding protocol independently specifies the hidden name,
no-read absent branch, exact object identity, and the fields of a failed
TypeError(:typeassert, "", IncludeMapexprs, value). The relation never calls
includeMapexprsQuery or Core typeassert to compute an expected result.
Julia source: base/loading.jl:2758-2762. -/
-- Source: base/loading.jl:2758-2762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_mapexprs(mod::Module)
--     root = moduleroot(mod)
--     isdefined(root, _include_mapexprs_name) || return nothing
--     return getglobal(root, _include_mapexprs_name)::IncludeMapexprs
-- end
-- /Source
def IncludeMapexprsBindingTrace {W L Mod D N P : Type}
    (ops : IncludeMapexprsQueryOps W L Mod D N P) (root : Mod) (world : W)
    (result : Except (DispatchError (ModuleQueryPayload L)) (GenericValue L)) (finalWorld : W)
    (events : List (ModuleQueryEvent W L)) : Prop :=
  let rootValue := ops.moduleValue root
  (∃ error,
    events = [.defined rootValue "#include_mapexprs#" world (.error error) finalWorld] ∧
    result = .error (.other (.inl error))) ∨
  (events = [.defined rootValue "#include_mapexprs#" world (.ok false) finalWorld] ∧
    result = .ok (.leaf ops.core.nothing)) ∨
  (∃ queriedWorld outcome,
    events = [.defined rootValue "#include_mapexprs#" world (.ok true) queriedWorld,
      .readGlobal rootValue (.symbol "#include_mapexprs#") queriedWorld outcome finalWorld] ∧
    match outcome with
    | .error error => result = .error (.other (.inr error))
    | .ok table =>
        (ops.core.isa table ops.tableType = true ∧ result = .ok table) ∨
        (ops.core.isa table ops.tableType = false ∧
          result = .error (.other (.inr (.leaf (ops.core.obj
            (.typeError (.symbol "typeassert") (.leaf (ops.core.str "")) ops.tableType table)))))))

/-- The query can diverge in the actual installed root loop, definedness
primitive, or reached global read. Typeassert is a terminating native check:
its failed result is a TypeError, never a fabricated divergence.
Julia source: base/loading.jl:2758-2762. -/
-- Source: base/loading.jl:2758-2762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_mapexprs(mod::Module)
--     root = moduleroot(mod)
--     isdefined(root, _include_mapexprs_name) || return nothing
--     return getglobal(root, _include_mapexprs_name)::IncludeMapexprs
-- end
-- /Source
def IncludeMapexprsQueryDiverges {W L Mod D N P : Type}
    (ops : IncludeMapexprsQueryOps W L Mod D N P) (module : Mod) (world : W) : Prop :=
  JuliaLean.base.runtime_internals.moduleroot ops.modules module world = none ∨
  ∃ root rootWorld,
    JuliaLean.base.runtime_internals.moduleroot ops.modules module world =
      some (.ok (root, rootWorld)) ∧
    (ops.types.isdefined (ops.moduleValue root) "#include_mapexprs#" rootWorld = none ∨
      ∃ queriedWorld,
        ops.types.isdefined (ops.moduleValue root) "#include_mapexprs#" rootWorld =
          some (.ok (true, queriedWorld)) ∧
        ops.core.getglobal (ops.moduleValue root) (.symbol "#include_mapexprs#") queriedWorld = none)

/-- For every module and arbitrary installed runtime/Core record, preserve
the root traversal observation, then enforce the independent binding protocol.
Failure worlds and exception payloads are checked across both carrier adapters;
wrongly typed bindings, absent bindings, returned identity and divergence are
included. No module-root or primitive correctness law is assumed.
Julia documentation: base/loading.jl:2743-2757 (include_mapexprs contract).
Julia source: base/loading.jl:2758-2762. -/
-- Source: base/loading.jl:2758-2762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_mapexprs(mod::Module)
--     root = moduleroot(mod)
--     isdefined(root, _include_mapexprs_name) || return nothing
--     return getglobal(root, _include_mapexprs_name)::IncludeMapexprs
-- end
-- /Source
def IncludeMapexprsCorrect : Prop :=
  ∀ (W L Mod D N P : Type) (ops : IncludeMapexprsQueryOps W L Mod D N P)
      (otherTypes : JuliaLean.base.runtime_internals.TypeOps
        (W × List (ModuleQueryEvent W L)) (GenericValue L) D N Mod P String)
      (otherCore : JuliaLean.base.boot.CoreOps (W × List (ModuleQueryEvent W L)) L)
      (module : Mod) (world : W),
    (∀ result finalWorld events,
      observe (includeMapexprsQuery (traceModuleQuery ops otherTypes otherCore) module)
        (world, []) = some (result, (finalWorld, events)) →
      ((∃ error,
        JuliaLean.base.runtime_internals.moduleroot ops.modules module world =
          some (.error (error, finalWorld)) ∧
        events = [] ∧ result = .error (.other (.inl error))) ∨
       (∃ root rootWorld,
        JuliaLean.base.runtime_internals.moduleroot ops.modules module world =
          some (.ok (root, rootWorld)) ∧
        IncludeMapexprsBindingTrace ops root rootWorld result finalWorld events))) ∧
    (observe (includeMapexprsQuery ops module) world = none ↔
      IncludeMapexprsQueryDiverges ops module world)

/-- Preserve selected Base/custom dispatch while instrumenting both actual
paths. The Base branch retains its native Ref read; custom code cannot forge
that protected read event or another method call.
Julia source: base/loading.jl:2781-2784. -/
-- Source: base/loading.jl:2781-2784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_dependency(path::AbstractString; track_content::Bool=true)
--     _include_dependency(Main, path, track_content=track_content, path_may_be_dir=true)
--     return nothing
-- end
-- /Source
def traceDependencyPublic {W L Mod Path : Type}
    (ops : DependencyPublicOps W L Mod Path)
    (otherCore : JuliaLean.base.boot.CoreOps
      (W × List (DependencyWrapperEvent W L Mod Path)) L) :
    DependencyPublicOps (W × List (DependencyWrapperEvent W L Mod Path)) L Mod Path where
  internalOps := traceDependencyWrapper ops.internalOps otherCore
  mainModule := ops.mainModule
  selection := ops.selection
  customInternal := fun module path content directory =>
    recordPackageStep (.customInternal module path content directory)
      (ops.customInternal module path content directory)

/-- The public call must use Main and enable directory paths. Exactly the
selected internal path runs; all successful values become actual nothing,
while any exception and its final world are unchanged.
Julia source: base/loading.jl:2781-2784. -/
-- Source: base/loading.jl:2781-2784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_dependency(path::AbstractString; track_content::Bool=true)
--     _include_dependency(Main, path, track_content=track_content, path_may_be_dir=true)
--     return nothing
-- end
-- /Source
def DependencyPublicTrace {W L Mod Path : Type}
    (ops : DependencyPublicOps W L Mod Path) (path : Path) (content : Bool) (world : W)
    (result : Except (DispatchError (GenericValue L)) (GenericValue L)) (finalWorld : W)
    (events : List (DependencyWrapperEvent W L Mod Path)) : Prop :=
  let nativeNothing : GenericValue L := .leaf ops.internalOps.core.nothing
  match ops.selection ops.mainModule path with
  | .base =>
      ∃ outcome,
        DependencyWrapperTrace ops.internalOps.trackDependenciesRef
          ops.internalOps.requireDependencies ops.mainModule path content true
          world outcome finalWorld events ∧
        result = outcome.map (fun _ => nativeNothing)
  | .custom =>
      ∃ outcome,
        events = [.customInternal ops.mainModule path content true world outcome finalWorld] ∧
        result = outcome.map (fun _ => nativeNothing)

/-- Only the selected internal execution can diverge. A successful value
never becomes a second call or a new source of nontermination.
Julia source: base/loading.jl:2781-2784. -/
-- Source: base/loading.jl:2781-2784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_dependency(path::AbstractString; track_content::Bool=true)
--     _include_dependency(Main, path, track_content=track_content, path_may_be_dir=true)
--     return nothing
-- end
-- /Source
def DependencyPublicDiverges {W L Mod Path : Type}
    (ops : DependencyPublicOps W L Mod Path) (path : Path) (content : Bool) (world : W) : Prop :=
  match ops.selection ops.mainModule path with
  | .base => DependencyWrapperDiverges ops.internalOps ops.mainModule path content true world
  | .custom => observe (ops.customInternal ops.mainModule path content true) world = none

/-- Full AbstractString-domain forwarding, success discard and error/effect
transparency, including Base/custom dispatch and arbitrary delegated results.
The native Main identity and true directory keyword are required independently
of the implementation, and the omitted track_content argument is checked as
true. No correctness or termination law is assumed for a selected method.
Julia documentation: base/loading.jl:2766-2780.
Julia source: base/loading.jl:2781-2784. -/
-- Source: base/loading.jl:2781-2784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function include_dependency(path::AbstractString; track_content::Bool=true)
--     _include_dependency(Main, path, track_content=track_content, path_may_be_dir=true)
--     return nothing
-- end
-- /Source
def IncludeDependencyPublicCorrect : Prop :=
  ∀ (W L Mod Path : Type) (ops : DependencyPublicOps W L Mod Path)
      (otherCore : JuliaLean.base.boot.CoreOps
        (W × List (DependencyWrapperEvent W L Mod Path)) L)
      (path : Path) (content : Bool) (world : W),
    (∀ result finalWorld events,
      observe (includeDependencyPublic (traceDependencyPublic ops otherCore) path content)
        (world, []) = some (result, (finalWorld, events)) →
      DependencyPublicTrace ops path content world result finalWorld events) ∧
    (observe (includeDependencyPublic ops path content) world = none ↔
      DependencyPublicDiverges ops path content world) ∧
    (∀ result finalWorld events,
      observe (includeDependencyPublic (traceDependencyPublic ops otherCore) path)
        (world, []) = some (result, (finalWorld, events)) →
      DependencyPublicTrace ops path true world result finalWorld events)

/-- One protected selected-print observation retains the original IO,
native String argument, arbitrary return/error and complete effect world.
Julia source: base/loading.jl:2788-2790. -/
-- Source: base/loading.jl:2788-2790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, ex::PrecompilableError)
--     print(io, "Error when precompiling module, potentially caused by a __precompile__(false) declaration in the module.")
-- end
-- /Source
inductive PrecompilableShowEvent (E W IO R : Type) where
  | print (io : IO) (text : JuliaLean.Strings.JStr) (before : W)
      (outcome : Except (DispatchError E) R) (after : W)

/-- Observe the selected two-argument print call without constraining its
return type, error, IO effects or termination.
Julia source: base/loading.jl:2788-2790. -/
-- Source: base/loading.jl:2788-2790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, ex::PrecompilableError)
--     print(io, "Error when precompiling module, potentially caused by a __precompile__(false) declaration in the module.")
-- end
-- /Source
def tracePrecompilableShow {E W IO R : Type}
    (ops : PrecompilableShowOps (ObservationM E W) IO R) :
    PrecompilableShowOps (ObservationM E (W × List (PrecompilableShowEvent E W IO R))) IO R where
  print := fun io text => recordPackageStep (.print io text) (ops.print io text)

/-- For every IO subtype and selected print method, exactly one call gets
the original stream and the independently specified literal bytes. Its entire
result/error/world is show's observation. Arbitrary non-nothing results are
retained, and the divergence clause does not assume print terminates.
Julia source: base/loading.jl:2788-2790. -/
-- Source: base/loading.jl:2788-2790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, ex::PrecompilableError)
--     print(io, "Error when precompiling module, potentially caused by a __precompile__(false) declaration in the module.")
-- end
-- /Source
def ShowPrecompilableErrorCorrect : Prop :=
  ∀ (E W IO R : Type) (ops : PrecompilableShowOps (ObservationM E W) IO R)
      (io : IO) (ex : JuliaLean.base.loading.PrecompilableError) (world : W),
    (∀ result finalWorld events,
      observe (showPrecompilableError (tracePrecompilableShow ops) io ex) (world, []) =
        some (result, (finalWorld, events)) →
      ∃ text : JuliaLean.Strings.JStr,
        text.bytes = "Error when precompiling module, potentially caused by a __precompile__(false) declaration in the module.".toUTF8.toList ∧
        events = [.print io text world result finalWorld]) ∧
    (observe (showPrecompilableError ops io ex) world = none ↔
      ∃ text : JuliaLean.Strings.JStr,
        text.bytes = "Error when precompiling module, potentially caused by a __precompile__(false) declaration in the module.".toUTF8.toList ∧
        observe (ops.print io text) world = none)




/-- Protected observations distinguish four-argument forwarding from
selected custom three-argument dispatch and retain exact objects and outcomes.
Julia source: base/loading.jl:3472-3473.
Julia documentation: doc/src/manual/methods.md:885-911. -/
-- Source: base/loading.jl:3472-3473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- include_string(m::Module, txt::AbstractString, fname::AbstractString="string") =
--     include_string(identity, m, txt, fname)
-- /Source
inductive IncludeIdentityEvent (E Mod Custom R : Type) where
  | forward (function : IncludeIdentityFunction) (mod : Mod)
      (code filename : IncludeStringValue Custom) (outcome : Except (DispatchError E) R)
  | custom (mod : Mod) (code filename : IncludeStringValue Custom)
      (outcome : Except (DispatchError E) R)

/-- Retain method-selection metadata while protecting both call kinds.
Selected code cannot forge these observations.
Julia source: base/loading.jl:3472-3473.
Julia documentation: doc/src/manual/methods.md:885-911. -/
-- Source: base/loading.jl:3472-3473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- include_string(m::Module, txt::AbstractString, fname::AbstractString="string") =
--     include_string(identity, m, txt, fname)
-- /Source
def traceIncludeIdentity {E W Mod Custom R : Type}
    (ops : IncludeIdentityOps (ObservationM E W) Mod Custom R) :
    IncludeIdentityOps
      (ObservationM E (W × List (IncludeIdentityEvent E Mod Custom R))) Mod Custom R where
  includeString := fun function mod code filename =>
    recordResult (.forward function mod code filename) (ops.includeString function mod code filename)
  explicitSelection := ops.explicitSelection
  customExplicit := fun mod code filename =>
    recordResult (.custom mod code filename) (ops.customExplicit mod code filename)

/-- Full-domain forwarding/default invariant. Explicit entry makes one
identity-forwarding call. The optional overload inserts the native literal and
performs longer-arity dispatch: Base selection makes one four-argument call;
custom selection makes one three-argument call. Whole observations retain every
return, error, world and divergence, with no callee law or subtype restriction.
Julia source: base/loading.jl:3472-3473.
Julia documentation: doc/src/manual/methods.md:885-911. -/
-- Source: base/loading.jl:3472-3473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- include_string(m::Module, txt::AbstractString, fname::AbstractString="string") =
--     include_string(identity, m, txt, fname)
-- /Source
def IncludeStringIdentityCorrect : Prop :=
  includeDefaultFilename.bytes = [115, 116, 114, 105, 110, 103] ∧
  ∀ (E W Mod Custom R : Type)
      (ops : IncludeIdentityOps (ObservationM E W) Mod Custom R)
      (mod : Mod) (code filename : IncludeStringValue Custom) (world : W),
    observe (includeStringIdentity ops mod code filename) world =
      observe (ops.includeString .identity mod code filename) world ∧
    (∀ result finalWorld events,
      observe (includeStringIdentity (traceIncludeIdentity ops) mod code filename) (world, []) =
        some (result, (finalWorld, events)) →
      events = [.forward .identity mod code filename result]) ∧
    (let nativeFilename : JuliaLean.Strings.JStr := ⟨[115, 116, 114, 105, 110, 103], by decide⟩
     match ops.explicitSelection mod code (.native nativeFilename) with
     | .base =>
         observe (includeStringIdentityDefault ops mod code) world =
           observe (ops.includeString .identity mod code (.native nativeFilename)) world ∧
         (∀ result finalWorld events,
           observe (includeStringIdentityDefault (traceIncludeIdentity ops) mod code) (world, []) =
             some (result, (finalWorld, events)) →
           events = [.forward .identity mod code (.native nativeFilename) result])
     | .custom =>
         observe (includeStringIdentityDefault ops mod code) world =
           observe (ops.customExplicit mod code (.native nativeFilename)) world ∧
         (∀ result finalWorld events,
           observe (includeStringIdentityDefault (traceIncludeIdentity ops) mod code) (world, []) =
             some (result, (finalWorld, events)) →
           events = [.custom mod code (.native nativeFilename) result]))

/-- Protected observations distinguish both property reads, interpolation
and the final selected error call, with their complete outcomes and worlds.
Julia source: base/loading.jl:3672-3676. -/
-- Source: base/loading.jl:3672-3676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_package_module_loaded_error(pkg)
--     # match compilecache error type for non-125 errors
--     error("package `$(pkg.name)` did not define the expected \
--           module `$(pkg.name)`, check for typos in package module name")
-- end
-- /Source
inductive PackageLoadedErrorEvent (E W P Name Text R : Type) where
  | name (pkg : P) (before : W) (outcome : Except (DispatchError E) Name) (after : W)
  | string («prefix» : JuliaLean.Strings.JStr) (firstName : Name)
      (middle : JuliaLean.Strings.JStr) (secondName : Name) (suffix : JuliaLean.Strings.JStr)
      (before : W) (outcome : Except (DispatchError E) Text) (after : W)
  | error (message : Text) (before : W) (outcome : Except (DispatchError E) R) (after : W)

/-- Arbitrary selected implementations cannot forge this protected log.
Julia source: base/loading.jl:3672-3676. -/
-- Source: base/loading.jl:3672-3676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_package_module_loaded_error(pkg)
--     # match compilecache error type for non-125 errors
--     error("package `$(pkg.name)` did not define the expected \
--           module `$(pkg.name)`, check for typos in package module name")
-- end
-- /Source
def tracePackageLoadedError {E W P Name Text R : Type}
    (ops : PackageLoadedErrorOps (ObservationM E W) P Name Text R) :
    PackageLoadedErrorOps
      (ObservationM E (W × List (PackageLoadedErrorEvent E W P Name Text R))) P Name Text R where
  getName := fun pkg => recordPackageStep (.name pkg) (ops.getName pkg)
  string := fun «prefix» firstName middle secondName suffix =>
    recordPackageStep (.string «prefix» firstName middle secondName suffix)
      (ops.string «prefix» firstName middle secondName suffix)
  error := fun message => recordPackageStep (.error message) (ops.error message)

/-- Source-code-unit characterization of the diagnostic segments.
These are mathematical lists in a property, not unbounded Julia Strings.
Julia source: base/loading.jl:3672-3676. -/
-- Source: base/loading.jl:3672-3676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_package_module_loaded_error(pkg)
--     # match compilecache error type for non-125 errors
--     error("package `$(pkg.name)` did not define the expected \
--           module `$(pkg.name)`, check for typos in package module name")
-- end
-- /Source
def LoadedErrorSegments («prefix» middle suffix : JuliaLean.Strings.JStr) : Prop :=
  «prefix».bytes = [112, 97, 99, 107, 97, 103, 101, 32, 96] ∧
  middle.bytes = [96, 32, 100, 105, 100, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 101,
    32, 116, 104, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 32, 96] ∧
  suffix.bytes = [96, 44, 32, 99, 104, 101, 99, 107, 32, 102, 111, 114, 32, 116, 121, 112, 111, 115,
    32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 109, 111, 100, 117, 108, 101, 32, 110, 97, 109, 101]

/-- Independent full-domain diagnostic invariant: read the original package
twice before any interpolation; pass both possibly distinct results with the
exact literal segments; then pass the actual constructed message to the selected
error call. Every reached failure, state change and arbitrary final return is
preserved, and divergence occurs exactly at a reached divergent call. No getter,
string or error correctness law is assumed.
Julia source: base/loading.jl:3672-3676. -/
-- Source: base/loading.jl:3672-3676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_package_module_loaded_error(pkg)
--     # match compilecache error type for non-125 errors
--     error("package `$(pkg.name)` did not define the expected \
--           module `$(pkg.name)`, check for typos in package module name")
-- end
-- /Source
def PackageLoadedErrorCorrect : Prop :=
  LoadedErrorSegments loadedErrorPrefix loadedErrorMiddle loadedErrorSuffix ∧
  ∀ (E W P Name Text R : Type)
      (ops : PackageLoadedErrorOps (ObservationM E W) P Name Text R) (pkg : P) (world : W),
    (∀ result finalWorld events,
      observe (checkPackageModuleLoadedError (tracePackageLoadedError ops) pkg) (world, []) =
        some (result, (finalWorld, events)) →
      ((∃ error, events = [.name pkg world (.error error) finalWorld] ∧ result = .error error) ∨
       (∃ firstName w1 error,
         events = [.name pkg world (.ok firstName) w1, .name pkg w1 (.error error) finalWorld] ∧
         result = .error error) ∨
       (∃ firstName secondName w1 w2 «prefix» middle suffix error,
         LoadedErrorSegments «prefix» middle suffix ∧
         events = [.name pkg world (.ok firstName) w1, .name pkg w1 (.ok secondName) w2,
           .string «prefix» firstName middle secondName suffix w2 (.error error) finalWorld] ∧
         result = .error error) ∨
       (∃ firstName secondName message w1 w2 w3 «prefix» middle suffix,
         LoadedErrorSegments «prefix» middle suffix ∧
         events = [.name pkg world (.ok firstName) w1, .name pkg w1 (.ok secondName) w2,
           .string «prefix» firstName middle secondName suffix w2 (.ok message) w3,
           .error message w3 result finalWorld]))) ∧
    (observe (checkPackageModuleLoadedError ops pkg) world = none ↔
      observe (ops.getName pkg) world = none ∨
      (∃ firstName w1,
        observe (ops.getName pkg) world = some (.ok firstName, w1) ∧
        observe (ops.getName pkg) w1 = none) ∨
      (∃ firstName secondName w1 w2,
        observe (ops.getName pkg) world = some (.ok firstName, w1) ∧
        observe (ops.getName pkg) w1 = some (.ok secondName, w2) ∧
        observe (ops.string loadedErrorPrefix firstName loadedErrorMiddle secondName loadedErrorSuffix) w2 = none) ∨
      (∃ firstName secondName message w1 w2 w3,
        observe (ops.getName pkg) world = some (.ok firstName, w1) ∧
        observe (ops.getName pkg) w1 = some (.ok secondName, w2) ∧
        observe (ops.string loadedErrorPrefix firstName loadedErrorMiddle secondName loadedErrorSuffix) w2 =
          some (.ok message, w3) ∧
        observe (ops.error message) w3 = none))


/-- Protected terminal observations of both open calls.
Julia source: base/loading.jl:4370-4370. -/
-- Source: base/loading.jl:4370-4370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- preferences_blob(f::IO, cachefile::AbstractString) = parse_cache_header(f, cachefile)[5]
-- /Source
inductive PreferenceBlobStreamEvent (E W IO Path Header R : Type) where
  | parse (io : IO) (path : Path) (before : W)
      (outcome : Except (DispatchError E) Header) (after : W)
  | index (header : Header) (index : JInt .i64) (before : W)
      (outcome : Except (DispatchError E) R) (after : W)

/-- Add an inaccessible event log without changing selected callees.
Julia source: base/loading.jl:4370-4370. -/
-- Source: base/loading.jl:4370-4370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- preferences_blob(f::IO, cachefile::AbstractString) = parse_cache_header(f, cachefile)[5]
-- /Source
def tracePreferenceBlobStream {E W IO Path Header R : Type}
    (ops : PreferenceBlobStreamOps (ObservationM E W) IO Path Header R) :
    PreferenceBlobStreamOps
      (ObservationM E (W × List (PreferenceBlobStreamEvent E W IO Path Header R))) IO Path Header R where
  parseHeader := fun io path => recordPackageStep (.parse io path) (ops.parseHeader io path)
  getindex := fun header index => recordPackageStep (.index header index) (ops.getindex header index)

/-- Full-domain parse-before-index protocol. A failed parse prevents
indexing. Every successful parse value is forwarded unchanged, at native index
five; the selected indexing result, error and final world are returned unchanged.
Divergence occurs exactly in a reached call; no callee correctness law is used.
Julia source: base/loading.jl:4370-4370. -/
-- Source: base/loading.jl:4370-4370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- preferences_blob(f::IO, cachefile::AbstractString) = parse_cache_header(f, cachefile)[5]
-- /Source
def PreferenceBlobStreamCorrect : Prop :=
  ∀ (E W IO Path Header R : Type)
      (ops : PreferenceBlobStreamOps (ObservationM E W) IO Path Header R)
      (io : IO) (path : Path) (world : W),
    (∀ result finalWorld events,
      observe (preferencesBlobStream (tracePreferenceBlobStream ops) io path) (world, []) =
        some (result, (finalWorld, events)) →
      ((∃ error, events = [.parse io path world (.error error) finalWorld] ∧ result = .error error) ∨
       (∃ header nextWorld, ∃ (index : JInt .i64), index.val = 5 ∧
         events = [.parse io path world (.ok header) nextWorld,
           .index header index nextWorld result finalWorld]))) ∧
    (observe (preferencesBlobStream ops io path) world = none ↔
      observe (ops.parseHeader io path) world = none ∨
      ∃ header nextWorld,
        observe (ops.parseHeader io path) world = some (.ok header, nextWorld) ∧
        observe (ops.getindex header (JInt.lit .i64 5)) nextWorld = none)

/-- The selected lookup receives the exact factory, dictionary and key;
the event preserves its before/after worlds and unrestricted returned value.
Julia source: base/loading.jl:4490-4496. -/
-- Source: base/loading.jl:4490-4496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function filter_preferences(prefs::Dict{String, Any}, pkg_name)
--     if pkg_name === nothing
--         return prefs
--     else
--         return get(Dict{String, Any}, prefs, pkg_name)::Dict{String, Any}
--     end
-- end
-- /Source
inductive FilterPreferenceEvent (W L : Type) where
  | get (factory prefs key : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)

/-- Copy every reached pure Core primitive and protect the lookup event.
Unused otherCore fields are universally arbitrary and are never called.
Julia source: base/loading.jl:4490-4496. -/
-- Source: base/loading.jl:4490-4496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function filter_preferences(prefs::Dict{String, Any}, pkg_name)
--     if pkg_name === nothing
--         return prefs
--     else
--         return get(Dict{String, Any}, prefs, pkg_name)::Dict{String, Any}
--     end
-- end
-- /Source
def traceFilterPreferences {W L : Type} (ops : FilterPreferenceOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (FilterPreferenceEvent W L)) L) :
    FilterPreferenceOps (W × List (FilterPreferenceEvent W L)) L where
  core := { otherCore with
    toLeafOps := ops.core.toLeafOps
    same := ops.core.same
    isa := ops.core.isa
    obj := ops.core.obj
    str := ops.core.str }
  dictType := ops.dictType
  getDefaultFactory := fun factory prefs key =>
    recordPackageStep (.get factory prefs key) (ops.getDefaultFactory factory prefs key)

/-- Full-domain alias-preservation and selected-lookup invariant. The
nothing branch performs no lookup and returns the identical preferences object
with unchanged world. Other keys include arbitrary Symbols, numbers and custom
objects. A lookup failure is propagated; a successful lookup is returned exactly
when isa holds, and otherwise raises TypeError(:typeassert,"",Dict{String,Any},value)
with no rollback. No property of get or the Core primitive outcomes is assumed.
Julia source: base/loading.jl:4490-4496. -/
-- Source: base/loading.jl:4490-4496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function filter_preferences(prefs::Dict{String, Any}, pkg_name)
--     if pkg_name === nothing
--         return prefs
--     else
--         return get(Dict{String, Any}, prefs, pkg_name)::Dict{String, Any}
--     end
-- end
-- /Source
def FilterPreferencesCorrect : Prop :=
  ∀ (W L : Type) (ops : FilterPreferenceOps W L)
      (otherCore : JuliaLean.base.boot.CoreOps (W × List (FilterPreferenceEvent W L)) L)
      (prefs pkgName : GenericValue L) (world : W),
    (∀ result finalWorld events,
      observe (filterPreferences (traceFilterPreferences ops otherCore) prefs pkgName) (world, []) =
        some (result, (finalWorld, events)) →
      ((ops.core.same pkgName (.leaf ops.core.nothing) = true ∧
        result = .ok prefs ∧ finalWorld = world ∧ events = []) ∨
       (ops.core.same pkgName (.leaf ops.core.nothing) = false ∧
        ∃ outcome,
          events = [.get ops.dictType prefs pkgName world outcome finalWorld] ∧
          match outcome with
          | .error error => result = .error error
          | .ok value =>
              (ops.core.isa value ops.dictType = true ∧ result = .ok value) ∨
              (ops.core.isa value ops.dictType = false ∧
                result = .error (.other (.leaf (ops.core.obj
                  (.typeError (.symbol "typeassert") (.leaf (ops.core.str "")) ops.dictType value)))))))) ∧
    (observe (filterPreferences ops prefs pkgName) world = none ↔
      ops.core.same pkgName (.leaf ops.core.nothing) = false ∧
      observe (ops.getDefaultFactory ops.dictType prefs pkgName) world = none)

/-- Protected wrapped-classifier observations retain the exact Symbol, object,
result/error, and before/after worlds. The mutable world cannot forge the log.
Julia source: base/loading.jl:2791-2793. -/
-- Source: base/loading.jl:2791-2793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- precompilableerror(ex::PrecompilableError) = true
-- precompilableerror(ex::WrappedException) = precompilableerror(ex.error)
-- precompilableerror(@nospecialize ex) = false
-- /Source
inductive WrappedPrecompileEvent (E W Wrapped Other ReturnOther : Type) where
  | property (wrapped : Wrapped) (name : JuliaLean.base.expr.Sym) (before : W)
      (outcome : Except (DispatchError E) (WrappedPrecompileValue Wrapped Other)) (after : W)
  | customWrapped (wrapped : Wrapped) (before : W)
      (outcome : Except (DispatchError E) (DispatchValue ReturnOther)) (after : W)
  | customOther (value : Other) (before : W)
      (outcome : Except (DispatchError E) (DispatchValue ReturnOther)) (after : W)

/-- Instrument the open property access and custom classification leaves;
Base recursion and both native terminal methods remain the actual models.
Julia source: base/loading.jl:2791-2793. -/
-- Source: base/loading.jl:2791-2793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- precompilableerror(ex::PrecompilableError) = true
-- precompilableerror(ex::WrappedException) = precompilableerror(ex.error)
-- precompilableerror(@nospecialize ex) = false
-- /Source
def traceWrappedPrecompile {E W Wrapped Other ReturnOther : Type}
    (ops : WrappedPrecompileOps (ObservationM E W) Wrapped Other ReturnOther) :
    WrappedPrecompileOps
      (ObservationM E (W × List (WrappedPrecompileEvent E W Wrapped Other ReturnOther)))
      Wrapped Other ReturnOther where
  getproperty := fun wrapped name =>
    recordPackageStep (fun before outcome after => .property wrapped name before outcome after)
      (ops.getproperty wrapped name)
  wrappedSelection := ops.wrappedSelection
  otherSelection := ops.otherSelection
  customWrapped := fun wrapped =>
    recordPackageStep (fun before outcome after => .customWrapped wrapped before outcome after)
      (ops.customWrapped wrapped)
  customOther := fun value =>
    recordPackageStep (fun before outcome after => .customOther value before outcome after)
      (ops.customOther value)

/-- Independent observation language for every finite recursive chain. Each
entry first reads its original object's :error once. Successful Base-wrapper
edges preserve the next object's identity and world; only the documented
native terminal classes yield their fixed Booleans. All selected custom values,
exceptions, and terminal worlds are passed through without Bool coercion.
Julia source: base/loading.jl:2791-2793. -/
-- Source: base/loading.jl:2791-2793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- precompilableerror(ex::PrecompilableError) = true
-- precompilableerror(ex::WrappedException) = precompilableerror(ex.error)
-- precompilableerror(@nospecialize ex) = false
-- /Source
inductive WrappedPrecompileTrace {E W Wrapped Other ReturnOther : Type}
    (wrappedSelection : Wrapped → WrappedPrecompileSelection)
    (otherSelection : Other → WrappedPrecompileSelection) :
    Wrapped → W → Except (DispatchError E) (DispatchValue ReturnOther) → W →
      List (WrappedPrecompileEvent E W Wrapped Other ReturnOther) → Prop where
  | propertyError (wrapped : Wrapped) (world after : W) (error : DispatchError E) :
      WrappedPrecompileTrace wrappedSelection otherSelection wrapped world (.error error) after
        [.property wrapped "error" world (.error error) after]
  | precompilable (wrapped : Wrapped) (world after : W)
      (value : JuliaLean.base.loading.PrecompilableError) :
      WrappedPrecompileTrace wrappedSelection otherSelection wrapped world (.ok (.bool true)) after
        [.property wrapped "error" world (.ok (.precompilable value)) after]
  | fallback (wrapped : Wrapped) (world after : W) (value : Other)
      (selected : otherSelection value = .base) :
      WrappedPrecompileTrace wrappedSelection otherSelection wrapped world (.ok (.bool false)) after
        [.property wrapped "error" world (.ok (.other value)) after]
  | otherCustom (wrapped : Wrapped) (world fieldWorld after : W) (value : Other)
      (outcome : Except (DispatchError E) (DispatchValue ReturnOther))
      (selected : otherSelection value = .custom) :
      WrappedPrecompileTrace wrappedSelection otherSelection wrapped world outcome after
        [.property wrapped "error" world (.ok (.other value)) fieldWorld,
          .customOther value fieldWorld outcome after]
  | wrappedCustom (wrapped next : Wrapped) (world fieldWorld after : W)
      (outcome : Except (DispatchError E) (DispatchValue ReturnOther))
      (selected : wrappedSelection next = .custom) :
      WrappedPrecompileTrace wrappedSelection otherSelection wrapped world outcome after
        [.property wrapped "error" world (.ok (.wrapped next)) fieldWorld,
          .customWrapped next fieldWorld outcome after]
  | recursive (wrapped next : Wrapped) (world fieldWorld after : W)
      (outcome : Except (DispatchError E) (DispatchValue ReturnOther))
      (events : List (WrappedPrecompileEvent E W Wrapped Other ReturnOther))
      (selected : wrappedSelection next = .base)
      (tail : WrappedPrecompileTrace wrappedSelection otherSelection next fieldWorld
        outcome after events) :
      WrappedPrecompileTrace wrappedSelection otherSelection wrapped world outcome after
        (.property wrapped "error" world (.ok (.wrapped next)) fieldWorld :: events)

/-- Reachability through successful Base-wrapper edges. Objects may repeat and
worlds may change, so neither acyclicity nor immutable property contents is
assumed. The witnesses refer only to selected property-call observations.
Julia source: base/loading.jl:2792. -/
-- Source: base/loading.jl:2791-2793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- precompilableerror(ex::PrecompilableError) = true
-- precompilableerror(ex::WrappedException) = precompilableerror(ex.error)
-- precompilableerror(@nospecialize ex) = false
-- /Source
inductive WrappedPrecompileReach {E W Wrapped Other ReturnOther : Type}
    (ops : WrappedPrecompileOps (ObservationM E W) Wrapped Other ReturnOther)
    (initial : Wrapped) (world : W) : Wrapped → W → Prop where
  | start : WrappedPrecompileReach ops initial world initial world
  | step (current next : Wrapped) (before after : W)
      (reached : WrappedPrecompileReach ops initial world current before)
      (property : observe (ops.getproperty current "error") before =
        some (.ok (.wrapped next), after))
      (selected : ops.wrappedSelection next = .base) :
      WrappedPrecompileReach ops initial world next after

/-- A finite terminal observation exists at a reached object only when property
access throws, returns a native terminal class, or returns an object whose
selected custom classification terminates. A Base-wrapper edge is not terminal.
This is a reachability witness, not an executable expected-result classifier.
Julia source: base/loading.jl:2791-2793. -/
-- Source: base/loading.jl:2791-2793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- precompilableerror(ex::PrecompilableError) = true
-- precompilableerror(ex::WrappedException) = precompilableerror(ex.error)
-- precompilableerror(@nospecialize ex) = false
-- /Source
def WrappedPrecompileTerminal {E W Wrapped Other ReturnOther : Type}
    (ops : WrappedPrecompileOps (ObservationM E W) Wrapped Other ReturnOther)
    (wrapped : Wrapped) (world : W) : Prop :=
  (∃ error after, observe (ops.getproperty wrapped "error") world = some (.error error, after)) ∨
  (∃ value after, observe (ops.getproperty wrapped "error") world =
    some (.ok (.precompilable value), after)) ∨
  (∃ value after, observe (ops.getproperty wrapped "error") world = some (.ok (.other value), after) ∧
    (ops.otherSelection value = .base ∨
      (ops.otherSelection value = .custom ∧ (observe (ops.customOther value) after).isSome = true))) ∨
  (∃ next after, observe (ops.getproperty wrapped "error") world = some (.ok (.wrapped next), after) ∧
    ops.wrappedSelection next = .custom ∧ (observe (ops.customWrapped next) after).isSome = true)

/-- Full abstract WrappedException invariant, including missing/error-producing
properties, arbitrary custom returns, heap mutation, repeated objects, and
infinite cycles. Completed traces enforce exact source order, identity, and
error/world transparency. Trace erasure recovers the uninstrumented result.
Nontermination is equivalent to absence of a finite reachable terminal
observation, ruling out fuel errors, premature success, and spurious divergence.
Every carrier and selected action is quantified without correctness laws.
Julia documentation: base/boot.jl:581-595 (abstract wrappers and error fields).
Julia source: base/loading.jl:2791-2793. -/
-- Source: base/loading.jl:2791-2793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- precompilableerror(ex::PrecompilableError) = true
-- precompilableerror(ex::WrappedException) = precompilableerror(ex.error)
-- precompilableerror(@nospecialize ex) = false
-- /Source
def WrappedPrecompilableCorrect : Prop :=
  ∀ (E W Wrapped Other ReturnOther : Type)
      (ops : WrappedPrecompileOps (ObservationM E W) Wrapped Other ReturnOther)
      (wrapped : Wrapped) (world : W),
    let traced := observe (wrappedPrecompilableError (traceWrappedPrecompile ops) wrapped) (world, [])
    let plain := observe (wrappedPrecompilableError ops wrapped) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ outcome after events, traced = some (outcome, (after, events)) →
      WrappedPrecompileTrace ops.wrappedSelection ops.otherSelection wrapped world outcome after events) ∧
    (plain = none ↔ ¬ ∃ current before,
      WrappedPrecompileReach ops wrapped world current before ∧
      WrappedPrecompileTerminal ops current before)

/-- Protected primitive/dispatch observations for check_for_hint. Objects,
selectors, exceptions, returned values, and worlds retain their full runtime
representations; the two parent calls cannot be silently merged.
Julia source: base/loading.jl:2855-2865. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
inductive HintEvent (W L : Type) where
  | defined (object selector : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) Bool) (after : W)
  | field (object selector : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)
  | parent (object : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L)) (after : W)

/-- Protected Core observation with original worlds. The event uses precisely
the existing liftCoreAction error representation, retaining the complete thrown
runtime value. The native Core action itself is unchanged.
Julia source: base/loading.jl:2857,2859. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
def recordHintCore {W L A Event : Type}
    (event : W → Except (DispatchError (GenericValue L)) A → W → Event)
    (action : JuliaLean.base.boot.CoreM W L A) :
    JuliaLean.base.boot.CoreM (W × List Event) L A :=
  fun initial => do
    match ← action initial.1 with
    | .ok (value, after) =>
        pure (.ok (value, (after, initial.2 ++ [event initial.1 (.ok value) after])))
    | .error (error, after) =>
        pure (.error (error, (after, initial.2 ++ [event initial.1 (.error (.other error)) after])))

/-- Bind every reached Core operation to the original primitive interface and
instrument its observations. All unused Core fields are universally supplied
by otherCore, not filled with stubs or correctness assumptions. Pure Module,
Bool, String, and tuple primitives remain identical under instrumentation.
Julia source: base/loading.jl:2855-2865. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
def traceHint {W L : Type} (ops : HintOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (HintEvent W L)) L) :
    HintOps (W × List (HintEvent W L)) L where
  core := { otherCore with
    str := ops.core.str
    ofBool := ops.core.ofBool
    tuple := ops.core.tuple
    core := ops.core.core
    isa := ops.core.isa
    getfield := fun object selector =>
      recordHintCore (.field object selector) (ops.core.getfield object selector) }
  defined := { isdefined := fun object selector =>
    recordHintCore (.defined object selector) (ops.defined.isdefined object selector) }
  parentmodule := fun object => recordPackageStep (.parent object) (ops.parentmodule object)

/-- Independent exact native tuple shape. The Bool and text occupy their source
positions; the relation does not call hintTuple or the model literal helpers.
Julia source: base/loading.jl:2858,2860,2862. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
def HintTupleShape {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (found : Bool) (text : String) (value : GenericValue L) : Prop :=
  value = .leaf (core.tuple [.leaf (core.ofBool found), .leaf (core.str text)])

/-- Finite language of the second condition. The first parent result is used
only by isdefined. On true, a second parentmodule(into) call supplies the
getfield object, which may differ. Every reached failure is terminal with its
exact world; completed checks have the exact native parent/empty tuple shape.
Julia source: base/loading.jl:2859-2862. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
inductive HintParentTrace {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (into selector : GenericValue L) :
    W → Except (DispatchError (GenericValue L)) (GenericValue L) → W →
      List (HintEvent W L) → Prop where
  | firstError (world after : W) (error : DispatchError (GenericValue L)) :
      HintParentTrace core into selector world (.error error) after
        [.parent into world (.error error) after]
  | definedError (world parentWorld after : W) (parent : GenericValue L)
      (error : DispatchError (GenericValue L)) :
      HintParentTrace core into selector world (.error error) after
        [.parent into world (.ok parent) parentWorld,
          .defined parent selector parentWorld (.error error) after]
  | undefined (world parentWorld after : W) (parent value : GenericValue L)
      (shape : HintTupleShape core false "" value) :
      HintParentTrace core into selector world (.ok value) after
        [.parent into world (.ok parent) parentWorld,
          .defined parent selector parentWorld (.ok false) after]
  | secondError (world parentWorld definedWorld after : W) (parent : GenericValue L)
      (error : DispatchError (GenericValue L)) :
      HintParentTrace core into selector world (.error error) after
        [.parent into world (.ok parent) parentWorld,
          .defined parent selector parentWorld (.ok true) definedWorld,
          .parent into definedWorld (.error error) after]
  | fieldError (world parentWorld definedWorld secondWorld after : W)
      (firstParent secondParent : GenericValue L) (error : DispatchError (GenericValue L)) :
      HintParentTrace core into selector world (.error error) after
        [.parent into world (.ok firstParent) parentWorld,
          .defined firstParent selector parentWorld (.ok true) definedWorld,
          .parent into definedWorld (.ok secondParent) secondWorld,
          .field secondParent selector secondWorld (.error error) after]
  | module (world parentWorld definedWorld secondWorld after : W)
      (firstParent secondParent field value : GenericValue L)
      (isModule : core.isa field (JuliaLean.base.boot.coreV core "Module") = true)
      (shape : HintTupleShape core true ".." value) :
      HintParentTrace core into selector world (.ok value) after
        [.parent into world (.ok firstParent) parentWorld,
          .defined firstParent selector parentWorld (.ok true) definedWorld,
          .parent into definedWorld (.ok secondParent) secondWorld,
          .field secondParent selector secondWorld (.ok field) after]
  | nonModule (world parentWorld definedWorld secondWorld after : W)
      (firstParent secondParent field value : GenericValue L)
      (isModule : core.isa field (JuliaLean.base.boot.coreV core "Module") = false)
      (shape : HintTupleShape core false "" value) :
      HintParentTrace core into selector world (.ok value) after
        [.parent into world (.ok firstParent) parentWorld,
          .defined firstParent selector parentWorld (.ok true) definedWorld,
          .parent into definedWorld (.ok secondParent) secondWorld,
          .field secondParent selector secondWorld (.ok field) after]

/-- Whole source observation language. A false first definition check skips
its getfield. A true Module field returns immediately and cannot reach parent
lookup. Otherwise the complete second-condition language follows with the exact
world left by the first check. Both untyped input objects remain unchanged.
Julia source: base/loading.jl:2855-2865. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
inductive HintTrace {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (into selector : GenericValue L) :
    W → Except (DispatchError (GenericValue L)) (GenericValue L) → W →
      List (HintEvent W L) → Prop where
  | definedError (world after : W) (error : DispatchError (GenericValue L)) :
      HintTrace core into selector world (.error error) after
        [.defined into selector world (.error error) after]
  | undefined (world definedWorld after : W)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L))
      (events : List (HintEvent W L))
      (tail : HintParentTrace core into selector definedWorld outcome after events) :
      HintTrace core into selector world outcome after
        (.defined into selector world (.ok false) definedWorld :: events)
  | fieldError (world definedWorld after : W) (error : DispatchError (GenericValue L)) :
      HintTrace core into selector world (.error error) after
        [.defined into selector world (.ok true) definedWorld,
          .field into selector definedWorld (.error error) after]
  | module (world definedWorld after : W) (field value : GenericValue L)
      (isModule : core.isa field (JuliaLean.base.boot.coreV core "Module") = true)
      (shape : HintTupleShape core true "." value) :
      HintTrace core into selector world (.ok value) after
        [.defined into selector world (.ok true) definedWorld,
          .field into selector definedWorld (.ok field) after]
  | nonModule (world definedWorld fieldWorld after : W) (field : GenericValue L)
      (outcome : Except (DispatchError (GenericValue L)) (GenericValue L))
      (events : List (HintEvent W L))
      (isModule : core.isa field (JuliaLean.base.boot.coreV core "Module") = false)
      (tail : HintParentTrace core into selector fieldWorld outcome after events) :
      HintTrace core into selector world outcome after
        ([.defined into selector world (.ok true) definedWorld,
          .field into selector definedWorld (.ok field) fieldWorld] ++ events)

/-- Source call positions distinguish both parent calls and their independent
returned objects. These labels are observations, not runtime values.
Julia source: base/loading.jl:2857-2859. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
inductive HintPoint (L : Type) where
  | ownDefined
  | ownField
  | firstParent
  | parentDefined (parent : GenericValue L)
  | secondParent
  | parentField (parent : GenericValue L)

/-- Source-reachable call positions and worlds, based only on actual primitive
and selected parentmodule observations. False guards and non-Module fields
are the only edges to the second condition; errors have no outgoing edge.
Julia source: base/loading.jl:2855-2865. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
inductive HintReachable {W L : Type} (ops : HintOps W L)
    (into selector : GenericValue L) (initial : W) : HintPoint L → W → Prop where
  | start : HintReachable ops into selector initial .ownDefined initial
  | ownField (after : W)
      (defined : observe (liftCoreAction (ops.defined.isdefined into selector)) initial =
        some (.ok true, after)) :
      HintReachable ops into selector initial .ownField after
  | firstAfterUndefined (after : W)
      (defined : observe (liftCoreAction (ops.defined.isdefined into selector)) initial =
        some (.ok false, after)) :
      HintReachable ops into selector initial .firstParent after
  | firstAfterNonModule (before after : W) (field : GenericValue L)
      (reached : HintReachable ops into selector initial .ownField before)
      (read : observe (liftCoreAction (ops.core.getfield into selector)) before = some (.ok field, after))
      (isModule : ops.core.isa field (JuliaLean.base.boot.coreV ops.core "Module") = false) :
      HintReachable ops into selector initial .firstParent after
  | parentDefined (before after : W) (parent : GenericValue L)
      (reached : HintReachable ops into selector initial .firstParent before)
      (parentCall : observe (ops.parentmodule into) before = some (.ok parent, after)) :
      HintReachable ops into selector initial (.parentDefined parent) after
  | secondParent (before after : W) (parent : GenericValue L)
      (reached : HintReachable ops into selector initial (.parentDefined parent) before)
      (defined : observe (liftCoreAction (ops.defined.isdefined parent selector)) before =
        some (.ok true, after)) :
      HintReachable ops into selector initial .secondParent after
  | parentField (before after : W) (parent : GenericValue L)
      (reached : HintReachable ops into selector initial .secondParent before)
      (parentCall : observe (ops.parentmodule into) before = some (.ok parent, after)) :
      HintReachable ops into selector initial (.parentField parent) after

/-- Divergence must arise at a reached primitive or selected parentmodule call,
with the precise original selector, returned parent object, and current world.
No complete check_for_hint implementation supplies an expected observation.
Julia source: base/loading.jl:2855-2865. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
def HintDiverges {W L : Type} (ops : HintOps W L)
    (into selector : GenericValue L) (world : W) : Prop :=
  ∃ point before,
    HintReachable ops into selector world point before ∧
    match point with
    | .ownDefined => observe (liftCoreAction (ops.defined.isdefined into selector)) before = none
    | .ownField => observe (liftCoreAction (ops.core.getfield into selector)) before = none
    | .firstParent => observe (ops.parentmodule into) before = none
    | .parentDefined parent => observe (liftCoreAction (ops.defined.isdefined parent selector)) before = none
    | .secondParent => observe (ops.parentmodule into) before = none
    | .parentField parent => observe (liftCoreAction (ops.core.getfield parent selector)) before = none

/-- Full untyped caller invariant, including ordinary objects, malformed field
selectors, native integer indices, both separately effectful parent calls, all
errors, and divergence. Native tuples have the exact Boolean/text field order
and source literal bytes. Protected traces require exact call order, argument
identity, short-circuiting, and every terminal error/world. Trace erasure and
reachable-divergence equivalence exclude hidden effect changes or artificial
termination/nontermination. Runtime primitives and selected callees are all
universally quantified without laws. This covers the additive IsDefinedOps
primitive boundary, hintTuple/literals, and the installed Core adapter.
Julia documentation: base/docs/basedocs.jl:3014-3056;
doc/src/manual/control-flow.md:180-205,259-272,326-335.
Julia source: base/loading.jl:2855-2865. -/
-- Source: base/loading.jl:2855-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_for_hint(into, mod)
--     return begin
--         if isdefined(into, mod) && getfield(into, mod) isa Module
--             true, "."
--         elseif isdefined(parentmodule(into), mod) && getfield(parentmodule(into), mod) isa Module
--             true, ".."
--         else
--             false, ""
--         end
--     end
-- end
-- /Source
def CheckForHintCorrect : Prop :=
  hintDot.text.toUTF8.toList = [46] ∧
  hintParentDots.text.toUTF8.toList = [46, 46] ∧
  hintEmpty.text.toUTF8.toList = [] ∧
  ∀ (W L : Type) (ops : HintOps W L)
      (otherCore : JuliaLean.base.boot.CoreOps (W × List (HintEvent W L)) L)
      (into selector : GenericValue L) (world : W),
    let traced := observe (checkForHint (traceHint ops otherCore) into selector) (world, [])
    let plain := observe (checkForHint ops into selector) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ outcome after events, traced = some (outcome, (after, events)) →
      HintTrace ops.core into selector world outcome after events) ∧
    (plain = none ↔ HintDiverges ops into selector world)

/-- Result kinds separate unfixed Julia values, both ABI observations,
the native Ref{String} foreign result, and the arbitrary constructor result.
These are protected observation metadata, not runtime Julia dispatch tags.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
inductive ImageParseKind where
  | value
  | pointer
  | int32
  | nativeString
  | result

/-- The already installed runtime assertion carrier keeps both valid
native values and every wrong-type result observable.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseResponse (V R : Type) : ImageParseKind → Type
  | .value => V
  | .pointer =>
      JuliaLean.base.abstractarray.Models1Group1.TypeAssertion ImageBytePointer V
  | .int32 =>
      JuliaLean.base.abstractarray.Models1Group1.TypeAssertion (JInt .i32) V
  | .nativeString => JuliaLean.Strings.JStr
  | .result => R

/-- Requests retain exact source arguments and group both GC owners
with each operation performed in the foreign-call preservation region. The
native read type and conversion target are fixed by the constructor name.
No request stands for the parse body or an entire conversion helper.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
inductive ImageParseRequest (IO V : Type) : ImageParseKind → Type where
  | readInt32 (io : IO) : ImageParseRequest IO V .value
  | multiply (factor : JInt .i64) (nwords : V) : ImageParseRequest IO V .value
  | readCount (io : IO) (count : V) : ImageParseRequest IO V .value
  | constructString (value : V) : ImageParseRequest IO V .value
  | cconvertPointer (value : V) : ImageParseRequest IO V .value
  | cconvertInt32 (value : V) : ImageParseRequest IO V .value
  | unsafeConvertPointer (owners : ImageCallOwners V) (owner : V) :
      ImageParseRequest IO V .pointer
  | unsafeConvertInt32 (owners : ImageCallOwners V) (owner : V) :
      ImageParseRequest IO V .int32
  | featureBitsToString (owners : ImageCallOwners V) (pointer : ImageBytePointer)
      (nwords : JInt .i32) : ImageParseRequest IO V .nativeString
  | constructImageTarget (name flags base extFeatures : V)
      (featuresEnabled featuresDisabled : JuliaLean.Strings.JStr) :
      ImageParseRequest IO V .result

/-- Every completed selected or foreign call records its typed result
or exact exception and its before/after worlds. The protected log is outside
the world supplied to arbitrary dispatch implementations.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
structure ImageParseEvent (E W IO V R : Type) where
  kind : ImageParseKind
  request : ImageParseRequest IO V kind
  before : W
  outcome : Except (ImageParseException E) (ImageParseResponse V R kind)
  after : W

/-- Instrument each leaf independently, preserving native typed C
arguments, the two owner values, every custom result and every exception.
No assertion or source control flow is hidden in the instrumentation.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def traceParseImage {E W IO V R : Type}
    (ops : ParseImageTargetOps
      (ObservationM (Sum JuliaLean.base.abstractarray.ArrayError E) W) IO V R) :
    ParseImageTargetOps
      (ObservationM (Sum JuliaLean.base.abstractarray.ArrayError E)
        (W × List (ImageParseEvent E W IO V R))) IO V R where
  readInt32 := fun io =>
    recordPackageStep
      (fun before outcome after => ⟨.value, .readInt32 io, before, outcome, after⟩)
      (ops.readInt32 io)
  multiply := fun factor nwords =>
    recordPackageStep
      (fun before outcome after => ⟨.value, .multiply factor nwords, before, outcome, after⟩)
      (ops.multiply factor nwords)
  readCount := fun io count =>
    recordPackageStep
      (fun before outcome after => ⟨.value, .readCount io count, before, outcome, after⟩)
      (ops.readCount io count)
  constructString := fun value =>
    recordPackageStep
      (fun before outcome after => ⟨.value, .constructString value, before, outcome, after⟩)
      (ops.constructString value)
  cconvertPointer := fun value =>
    recordPackageStep
      (fun before outcome after => ⟨.value, .cconvertPointer value, before, outcome, after⟩)
      (ops.cconvertPointer value)
  cconvertInt32 := fun value =>
    recordPackageStep
      (fun before outcome after => ⟨.value, .cconvertInt32 value, before, outcome, after⟩)
      (ops.cconvertInt32 value)
  unsafeConvertPointer := fun owners owner =>
    recordPackageStep
      (fun before outcome after =>
        ⟨.pointer, .unsafeConvertPointer owners owner, before, outcome, after⟩)
      (ops.unsafeConvertPointer owners owner)
  unsafeConvertInt32 := fun owners owner =>
    recordPackageStep
      (fun before outcome after =>
        ⟨.int32, .unsafeConvertInt32 owners owner, before, outcome, after⟩)
      (ops.unsafeConvertInt32 owners owner)
  featureBitsToString := fun owners pointer nwords =>
    recordPackageStep
      (fun before outcome after =>
        ⟨.nativeString, .featureBitsToString owners pointer nwords, before, outcome, after⟩)
      (ops.featureBitsToString owners pointer nwords)
  constructImageTarget := fun name flags base extFeatures featuresEnabled featuresDisabled =>
    recordPackageStep
      (fun before outcome after =>
        ⟨.result, .constructImageTarget name flags base extFeatures featuresEnabled featuresDisabled,
          before, outcome, after⟩)
      (ops.constructImageTarget name flags base extFeatures featuresEnabled featuresDisabled)

/-- Read a successful unfixed value from a protected earlier event.
There is no default value for an absent, failing or differently typed event.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def imageParseValueAt {E W IO V R : Type}
    (events : List (ImageParseEvent E W IO V R)) (index : Nat) : Option V :=
  match events[index]? with
  | some ⟨.value, _, _, .ok value, _⟩ => some value
  | _ => none

/-- Read an accepted native pointer from a protected earlier unsafe
conversion. A rejected ABI tag is never coerced to an address.
Julia source: base/loading.jl:2166-2167. -/
-- Source: base/loading.jl:2166-2167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
-- /Source
def imageParsePointerAt {E W IO V R : Type}
    (events : List (ImageParseEvent E W IO V R)) (index : Nat) : Option ImageBytePointer :=
  match events[index]? with
  | some ⟨.pointer, _, _, .ok (.accepted value), _⟩ => some value
  | _ => none

/-- Read an accepted native Int32 from a protected earlier unsafe
conversion, without conversion or a fabricated fallback.
Julia source: base/loading.jl:2166-2167. -/
-- Source: base/loading.jl:2166-2167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
-- /Source
def imageParseInt32At {E W IO V R : Type}
    (events : List (ImageParseEvent E W IO V R)) (index : Nat) : Option (JInt .i32) :=
  match events[index]? with
  | some ⟨.int32, _, _, .ok (.accepted value), _⟩ => some value
  | _ => none

/-- Read the native String returned by one completed C call. Its
identity in the installed JStr representation is forwarded to the constructor.
Julia source: base/loading.jl:2166-2169. -/
-- Source: base/loading.jl:2166-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def imageParseStringAt {E W IO V R : Type}
    (events : List (ImageParseEvent E W IO V R)) (index : Nat) :
    Option JuliaLean.Strings.JStr :=
  match events[index]? with
  | some ⟨.nativeString, _, _, .ok value, _⟩ => some value
  | _ => none

/-- Independent causal argument constraints for the 24 observable
calls. Slot numbers count only selected calls and the actual C primitive,
not pure ABI assertions. Every reference is strictly to an earlier slot.
This is a predicate on recorded requests, not an executable expected-result
model: the factor is specified by its mathematical value 8, and all other
arguments must be the exact recorded earlier values. In particular the two
multiplications and both independent nwords conversions are required.
The two owner values must accompany both unsafe conversions and the C call.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseRequestAllowed {E W IO V R : Type}
    (io : IO) (events : List (ImageParseEvent E W IO V R)) (slot : Nat)
    {kind : ImageParseKind} (request : ImageParseRequest IO V kind) : Prop :=
  match request with
  | .readInt32 actualIO =>
      actualIO = io ∧ (slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 7 ∨ slot = 10)
  | .multiply factor nwords =>
      (slot = 3 ∨ slot = 5) ∧ factor.val = 8 ∧ imageParseValueAt events 2 = some nwords
  | .readCount actualIO count =>
      actualIO = io ∧
      ((slot = 4 ∧ imageParseValueAt events 3 = some count) ∨
       (slot = 6 ∧ imageParseValueAt events 5 = some count) ∨
       (slot = 8 ∧ imageParseValueAt events 7 = some count) ∨
       (slot = 11 ∧ imageParseValueAt events 10 = some count))
  | .constructString value =>
      (slot = 9 ∧ imageParseValueAt events 8 = some value) ∨
      (slot = 12 ∧ imageParseValueAt events 11 = some value)
  | .cconvertPointer value =>
      (slot = 13 ∧ imageParseValueAt events 4 = some value) ∨
      (slot = 18 ∧ imageParseValueAt events 6 = some value)
  | .cconvertInt32 value =>
      (slot = 14 ∨ slot = 19) ∧ imageParseValueAt events 2 = some value
  | .unsafeConvertPointer owners owner =>
      owner = owners.pointerOwner ∧
      ((slot = 15 ∧ imageParseValueAt events 13 = some owners.pointerOwner ∧
          imageParseValueAt events 14 = some owners.countOwner) ∨
       (slot = 20 ∧ imageParseValueAt events 18 = some owners.pointerOwner ∧
          imageParseValueAt events 19 = some owners.countOwner))
  | .unsafeConvertInt32 owners owner =>
      owner = owners.countOwner ∧
      ((slot = 16 ∧ imageParseValueAt events 13 = some owners.pointerOwner ∧
          imageParseValueAt events 14 = some owners.countOwner) ∨
       (slot = 21 ∧ imageParseValueAt events 18 = some owners.pointerOwner ∧
          imageParseValueAt events 19 = some owners.countOwner))
  | .featureBitsToString owners pointer nwords =>
      (slot = 17 ∧ imageParseValueAt events 13 = some owners.pointerOwner ∧
        imageParseValueAt events 14 = some owners.countOwner ∧
        imageParsePointerAt events 15 = some pointer ∧ imageParseInt32At events 16 = some nwords) ∨
      (slot = 22 ∧ imageParseValueAt events 18 = some owners.pointerOwner ∧
        imageParseValueAt events 19 = some owners.countOwner ∧
        imageParsePointerAt events 20 = some pointer ∧ imageParseInt32At events 21 = some nwords)
  | .constructImageTarget name flags base extFeatures featuresEnabled featuresDisabled =>
      slot = 23 ∧ imageParseValueAt events 9 = some name ∧
      imageParseValueAt events 0 = some flags ∧ imageParseValueAt events 1 = some base ∧
      imageParseValueAt events 12 = some extFeatures ∧
      imageParseStringAt events 17 = some featuresEnabled ∧
      imageParseStringAt events 22 = some featuresDisabled

/-- A completed operation permits a later call only after success and,
for an unsafe conversion, an accepted native ABI result. A wrong-type return
therefore stops the trace before the next unsafe conversion or C call.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseContinues {E W IO V R : Type} (event : ImageParseEvent E W IO V R) : Prop :=
  match event with
  | ⟨.value, _, _, .ok _, _⟩ => True
  | ⟨.pointer, _, _, .ok (.accepted _), _⟩ => True
  | ⟨.int32, _, _, .ok (.accepted _), _⟩ => True
  | ⟨.nativeString, _, _, .ok _, _⟩ => True
  | ⟨.result, _, _, .ok _, _⟩ => True
  | _ => False

/-- Continuous worlds make mutations before both selected-call errors
and generated ABI TypeErrors observable. Empty prefixes preserve their
initial world. This relation contains no Julia operation.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
inductive ImageParseWorldChain {E W IO V R : Type} :
    W → W → List (ImageParseEvent E W IO V R) → Prop where
  | empty (world : W) :
      ImageParseWorldChain (E := E) (IO := IO) (V := V) (R := R) world world []
  | step (event : ImageParseEvent E W IO V R) (finalWorld : W)
      (events : List (ImageParseEvent E W IO V R))
      (following : ImageParseWorldChain event.after finalWorld events) :
      ImageParseWorldChain event.before finalWorld (event :: events)

/-- Every observed call must satisfy the source's independent causal
slot constraints. In particular no extra call can appear after slot 23.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseCallOrder {E W IO V R : Type}
    (io : IO) (events : List (ImageParseEvent E W IO V R)) : Prop :=
  ∀ slot event, events[slot]? = some event →
    ImageParseRequestAllowed io events slot event.request

/-- The only terminal outcomes are an unchanged selected-call error,
a generated TypeError immediately after a rejected ABI result, or the
unchanged arbitrary final constructor value. All other successful calls
require continuation. The final world is checked separately by WorldChain.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseLastResult {E W IO V R : Type}
    (last : ImageParseEvent E W IO V R) (result : Except (ImageParseException E) R) : Prop :=
  let success : (kind : ImageParseKind) → ImageParseResponse V R kind → Prop :=
    fun kind => match kind with
    | .pointer => fun value => match value with
      | .rejected _ => result = .error .typeError
      | .accepted _ => False
    | .int32 => fun value => match value with
      | .rejected _ => result = .error .typeError
      | .accepted _ => False
    | .result => fun value => result = .ok value
    | .value => fun _ => False
    | .nativeString => fun _ => False
  match last.outcome with
  | .error error => result = .error error
  | .ok value => success last.kind value

/-- A terminal execution has a nonempty source-ordered trace, a
successful accepted prefix, and one legal terminal observation. This
independent relation detects early returns, delayed type assertions, calls
after failure, incorrect argument forwarding, owner loss and changed worlds.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseTerminal {E W IO V R : Type} (io : IO)
    (world : W) (result : Except (ImageParseException E) R) (finalWorld : W)
    (events : List (ImageParseEvent E W IO V R)) : Prop :=
  events.length ≤ 24 ∧ ImageParseCallOrder io events ∧
  ImageParseWorldChain world finalWorld events ∧
  ∃ («prefix» : List (ImageParseEvent E W IO V R)) (last : ImageParseEvent E W IO V R),
    events = «prefix» ++ [last] ∧
    (∀ event, event ∈ «prefix» → ImageParseContinues event) ∧
    ImageParseLastResult last result

/-- Interpret a single independently recorded request to formulate
reachability. No whole source method or conversion helper is interpreted here.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def imageParseRequestAction {E W IO V R : Type}
    (ops : ParseImageTargetOps
      (ObservationM (Sum JuliaLean.base.abstractarray.ArrayError E) W) IO V R)
    {kind : ImageParseKind} (request : ImageParseRequest IO V kind) :
    ObservationM (Sum JuliaLean.base.abstractarray.ArrayError E) W
      (ImageParseResponse V R kind) :=
  match request with
  | .readInt32 io => ops.readInt32 io
  | .multiply factor nwords => ops.multiply factor nwords
  | .readCount io count => ops.readCount io count
  | .constructString value => ops.constructString value
  | .cconvertPointer value => ops.cconvertPointer value
  | .cconvertInt32 value => ops.cconvertInt32 value
  | .unsafeConvertPointer owners owner => ops.unsafeConvertPointer owners owner
  | .unsafeConvertInt32 owners owner => ops.unsafeConvertInt32 owners owner
  | .featureBitsToString owners pointer nwords => ops.featureBitsToString owners pointer nwords
  | .constructImageTarget name flags base extFeatures featuresEnabled featuresDisabled =>
      ops.constructImageTarget name flags base extFeatures featuresEnabled featuresDisabled

/-- A reachability witness contains actual successful observations of
arbitrary selected callees, not assumed correctness laws. Every earlier ABI
assertion must have accepted. This prevents a divergent later call from being
claimed reachable after a selected failure or wrong-type unsafe return.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseReachedPrefix {E W IO V R : Type}
    (ops : ParseImageTargetOps
      (ObservationM (Sum JuliaLean.base.abstractarray.ArrayError E) W) IO V R)
    (io : IO) (world middle : W) (events : List (ImageParseEvent E W IO V R)) : Prop :=
  events.length < 24 ∧ ImageParseCallOrder io events ∧
  ImageParseWorldChain world middle events ∧
  ∀ event, event ∈ events →
    ImageParseContinues event ∧
    observe (imageParseRequestAction ops event.request) event.before =
      some (event.outcome, event.after)

/-- Nontermination has a reached-callee origin after a successful
prefix. The existential witness describes actual observations, includes the
foreign-call owner scope, and imposes no correctness premise on any callee.
Julia source: base/loading.jl:2156-2169. -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ImageParseDivergence {E W IO V R : Type}
    (ops : ParseImageTargetOps
      (ObservationM (Sum JuliaLean.base.abstractarray.ArrayError E) W) IO V R)
    (io : IO) (world : W) : Prop :=
  ∃ («prefix» : List (ImageParseEvent E W IO V R)) (middle : W)
      (kind : ImageParseKind) (request : ImageParseRequest IO V kind),
    ImageParseReachedPrefix ops io world middle «prefix» ∧
    ImageParseRequestAllowed io «prefix» «prefix».length request ∧
    observe (imageParseRequestAction ops request) middle = none

/-- Full-domain causal protocol for parse_image_target. The quantified
IO/read/arithmetic/String/conversion/constructor dispatch is unrestricted.
The protected log checks all 24 reached operation slots, both multiplications
with native 8 and original nwords, both String calls, all cconvert/unsafe
conversion ordering, the exact owner pairs and typed C arguments, and final
six-argument forwarding. The native assertions stop on their first wrong
result with TypeError and the already-mutated world. Other failures and the
arbitrary constructor result pass through unchanged. Divergence is equivalent
to a reached divergent selected or foreign operation.

This registration covers imageFeatureBitsToString, assertImageABI and the
exception adapter through every reached conversion branch, without a callee
correctness law or a fixed native read-result restriction.
Julia source: base/loading.jl:2156-2169.
Julia documentation: doc/src/manual/calling-c-and-fortran-code.md:246-276,710-727;
doc/src/devdocs/ast.md:497-506,530-564; doc/src/manual/functions.md (return values). -/
-- Source: base/loading.jl:2156-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse_image_target(io::IO)
--     flags = read(io, Int32)
--     base = read(io, Int32)
--     nwords = read(io, Int32)  # number of uint64_t feature words
--     feature_en_raw = read(io, 8*nwords)
--     feature_dis_raw = read(io, 8*nwords)
--     name_len = read(io, Int32)
--     name = String(read(io, name_len))
--     ext_features_len = read(io, Int32)
--     ext_features = String(read(io, ext_features_len))
--     features_en = @ccall jl_feature_bits_to_string(feature_en_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     features_dis = @ccall jl_feature_bits_to_string(feature_dis_raw::Ptr{UInt8}, nwords::Int32)::Ref{String}
--     ImageTarget(name, flags, base, ext_features, features_en, features_dis)
-- end
-- /Source
def ParseImageTargetCorrect : Prop :=
  ∀ (E W IO V R : Type)
      (ops : ParseImageTargetOps
        (ObservationM (Sum JuliaLean.base.abstractarray.ArrayError E) W) IO V R)
      (io : IO) (world : W),
    (observe (parseImageTarget (E := E) ops io) world =
      (observe (parseImageTarget (E := E) (traceParseImage ops) io) (world, [])).map
        (fun observation => (observation.1, observation.2.1))) ∧
    (∀ result finalWorld events,
      observe (parseImageTarget (E := E) (traceParseImage ops) io) (world, []) =
        some (result, (finalWorld, events)) →
      ImageParseTerminal io world result finalWorld events) ∧
    (observe (parseImageTarget (E := E) ops io) world = none ↔
      ImageParseDivergence ops io world)


/-- Protected observations retain complete call arguments, including
explicit scalar indices, both globals, and the whole builtin splat argument
list. These lists are observation metadata, not extra Julia allocations.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
inductive CompilerPathCall (L : Type) where
  | scalar (tup : CompilerPathValue L) (index : JInt .i64)
  | joinpath (bindir datarootdir : JuliaLean.Strings.JStr) (second : CompilerPathValue L)
  | lastindex (tup : CompilerPathValue L)
  | colon (first : JInt .i64) (last : CompilerPathValue L)
  | slice (tup range : CompilerPathValue L)
  | splat (iteration : CompilerPathValue L) (arguments : List (CompilerPathValue L))

/-- Selected-call errors and lifted Core errors share the existing
exception carrier without losing the Core value or its mutation world.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
structure CompilerPathEvent (W L : Type) where
  call : CompilerPathCall L
  before : W
  outcome : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L)
  after : W

/-- Protect observations of all six selected calls and the one genuine
Core builtin. Native prefix tuple construction keeps the same installed
representation. The remaining otherCore fields are never reached.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def traceCompilerPath {W L : Type} (ops : ExpandCompilerPathOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps
      (W × List (CompilerPathEvent W L)) (CompilerPathLeaf L)) :
    ExpandCompilerPathOps (W × List (CompilerPathEvent W L)) L where
  core := { otherCore with
    tuple := ops.core.tuple
    applyIterate := fun iteration arguments =>
      recordSortCoreStep
        (fun before outcome after =>
          ⟨.splat iteration arguments, before, outcome.mapError DispatchError.other, after⟩)
        (ops.core.applyIterate iteration arguments) }
  bindir := ops.bindir
  datarootdir := ops.datarootdir
  getindexScalar := fun tup index =>
    recordPackageStep (fun before outcome after => ⟨.scalar tup index, before, outcome, after⟩)
      (ops.getindexScalar tup index)
  joinpath := fun bindir datarootdir second =>
    recordPackageStep (fun before outcome after =>
      ⟨.joinpath bindir datarootdir second, before, outcome, after⟩)
      (ops.joinpath bindir datarootdir second)
  lastindex := fun tup =>
    recordPackageStep (fun before outcome after => ⟨.lastindex tup, before, outcome, after⟩)
      (ops.lastindex tup)
  colon := fun first last =>
    recordPackageStep (fun before outcome after => ⟨.colon first last, before, outcome, after⟩)
      (ops.colon first last)
  getindexSlice := fun tup range =>
    recordPackageStep (fun before outcome after => ⟨.slice tup range, before, outcome, after⟩)
      (ops.getindexSlice tup range)

/-- Read an actual prior successful result without inventing a value
for an absent or failed observation.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def compilerPathValueAt {W L : Type} (events : List (CompilerPathEvent W L))
    (index : Nat) : Option (CompilerPathValue L) :=
  match events[index]? with
  | some event => match event.outcome with
    | .ok value => some value
    | .error _ => none
  | none => none

/-- Independent causal constraints use mathematical indices 1, 2 and 3
and exact function-identity tags. The builtin receives only Core.tuple, the
actual native pair of earlier first/joined values, and the exact slice result.
This predicate checks observations rather than running another expansion.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def CompilerPathCallAllowed {W L : Type} (ops : ExpandCompilerPathOps W L)
    (tup : CompilerPathValue L) (events : List (CompilerPathEvent W L))
    (slot : Nat) (call : CompilerPathCall L) : Prop :=
  match call with
  | .scalar actual index =>
      actual = tup ∧ ((slot = 0 ∧ index.val = 1) ∨ (slot = 1 ∧ index.val = 2))
  | .joinpath bindir datarootdir second =>
      slot = 2 ∧ bindir = ops.bindir ∧ datarootdir = ops.datarootdir ∧
      compilerPathValueAt events 1 = some second
  | .lastindex actual => slot = 3 ∧ actual = tup
  | .colon first last =>
      slot = 4 ∧ first.val = 3 ∧ compilerPathValueAt events 3 = some last
  | .slice actual range =>
      slot = 5 ∧ actual = tup ∧ compilerPathValueAt events 4 = some range
  | .splat iteration arguments =>
      slot = 6 ∧ iteration = .leaf (.inl CompilerPathBuiltin.baseIterate) ∧
      ∃ first joined tail,
        compilerPathValueAt events 0 = some first ∧
        compilerPathValueAt events 2 = some joined ∧
        compilerPathValueAt events 5 = some tail ∧
        arguments = [.leaf (.inl CompilerPathBuiltin.coreTuple),
          .leaf (ops.core.tuple [first, joined]), tail]

/-- World continuity is explicit even when a selected call or native
splat fails. This observation relation performs no Julia operation.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
inductive CompilerPathWorldChain {W L : Type} :
    W → W → List (CompilerPathEvent W L) → Prop where
  | empty (world : W) : CompilerPathWorldChain (L := L) world world []
  | step (event : CompilerPathEvent W L) (finalWorld : W)
      (events : List (CompilerPathEvent W L))
      (following : CompilerPathWorldChain event.after finalWorld events) :
      CompilerPathWorldChain event.before finalWorld (event :: events)

/-- Every call has its original slot, operands and literal indices.
No additional operation can be appended after the builtin splat.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def CompilerPathCallOrder {W L : Type} (ops : ExpandCompilerPathOps W L)
    (tup : CompilerPathValue L) (events : List (CompilerPathEvent W L)) : Prop :=
  ∀ slot event, events[slot]? = some event →
    CompilerPathCallAllowed ops tup events slot event.call

/-- Fail-fast terminal protocol. All preceding calls succeeded; the
last observation is returned unchanged, including its world. A success
requires all seven operations, while a failure may stop at any reached slot.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def CompilerPathTerminal {W L : Type} (ops : ExpandCompilerPathOps W L)
    (tup : CompilerPathValue L) (world : W)
    (result : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L))
    (finalWorld : W) (events : List (CompilerPathEvent W L)) : Prop :=
  events.length ≤ 7 ∧ CompilerPathCallOrder ops tup events ∧
  CompilerPathWorldChain world finalWorld events ∧
  ∃ («prefix» : List (CompilerPathEvent W L)) (last : CompilerPathEvent W L),
    events = «prefix» ++ [last] ∧
    (∀ event, event ∈ «prefix» → ∃ value, event.outcome = .ok value) ∧
    last.outcome = result ∧
    (∀ value, result = .ok value → events.length = 7)

/-- Observe one recorded leaf to define actual reachability. The splat
case calls the installed Core primitive and existing exception adapter. This
is not an alternative implementation of expand_compiler_path.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def compilerPathCallAction {W L : Type} (ops : ExpandCompilerPathOps W L)
    (call : CompilerPathCall L) : CompilerPathM W L (CompilerPathValue L) :=
  match call with
  | .scalar tup index => ops.getindexScalar tup index
  | .joinpath bindir datarootdir second => ops.joinpath bindir datarootdir second
  | .lastindex tup => ops.lastindex tup
  | .colon first last => ops.colon first last
  | .slice tup range => ops.getindexSlice tup range
  | .splat iteration arguments => liftCoreAction (ops.core.applyIterate iteration arguments)

/-- Reachability consists of actual successful observations of all
earlier calls. No output law for indexing, colon, joinpath, iteration or Core
is imposed; earlier failures prevent a later divergent operation being reached.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def CompilerPathReachedPrefix {W L : Type} (ops : ExpandCompilerPathOps W L)
    (tup : CompilerPathValue L) (world middle : W)
    (events : List (CompilerPathEvent W L)) : Prop :=
  events.length < 7 ∧ CompilerPathCallOrder ops tup events ∧
  CompilerPathWorldChain world middle events ∧
  ∀ event, event ∈ events →
    (∃ value, event.outcome = .ok value) ∧
    observe (compilerPathCallAction ops event.call) event.before = some (event.outcome, event.after)

/-- Divergence has a reached selected-call or native-splat origin,
with all preceding effects and argument dependencies preserved.
Julia source: base/loading.jl:5196-5198. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def CompilerPathDivergence {W L : Type} (ops : ExpandCompilerPathOps W L)
    (tup : CompilerPathValue L) (world : W) : Prop :=
  ∃ («prefix» : List (CompilerPathEvent W L)) (middle : W) (call : CompilerPathCall L),
    CompilerPathReachedPrefix ops tup world middle «prefix» ∧
    CompilerPathCallAllowed ops tup «prefix» «prefix».length call ∧
    observe (compilerPathCallAction ops call) middle = none

/-- Full-domain protocol for arbitrary tup values, nonstandard indices,
custom joinpath/colon results and arbitrary sliced iterables. Protected events
require the seven ordered operations, exact indices and globals, unchanged
intermediate values, native two-element prefix tuple, exact Base.iterate and
Core.tuple identities, and correct splat argument grouping. Every reached
error and its mutation world survive; successful native splat results pass
through without coercion. Divergence has exactly a reached-leaf origin.
The property imposes no callee-correctness law and no fixed tuple shape.
Julia source: base/loading.jl:5196-5198.
Julia documentation: doc/src/manual/interfaces.md:150-158;
doc/src/manual/functions.md:667-714; base/boot.jl:1256-1257. -/
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def ExpandCompilerPathCorrect : Prop :=
  ∀ (W L : Type) (ops : ExpandCompilerPathOps W L)
      (otherCore : JuliaLean.base.boot.CoreOps
        (W × List (CompilerPathEvent W L)) (CompilerPathLeaf L))
      (tup : CompilerPathValue L) (world : W),
    (observe (expandCompilerPath ops tup) world =
      (observe (expandCompilerPath (traceCompilerPath ops otherCore) tup) (world, [])).map
        (fun observation => (observation.1, observation.2.1))) ∧
    (∀ result finalWorld events,
      observe (expandCompilerPath (traceCompilerPath ops otherCore) tup) (world, []) =
        some (result, (finalWorld, events)) →
      CompilerPathTerminal ops tup world result finalWorld events) ∧
    (observe (expandCompilerPath ops tup) world = none ↔
      CompilerPathDivergence ops tup world)


/-- Independent primitive-locality invariant with Boolean anchors. Changing
any runtime operations or identity answers except the answer for the actual
ordered input pair cannot change the fallback result. Constant-true and
constant-false interpretations establish polarity. This quantifies over all
heterogeneous values and does not assume an equality law for Core.same.
Julia source: base/loading.jl:4866-4866. -/
-- Source: base/loading.jl:4866-4866 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toml_egal(@nospecialize(A), @nospecialize(B)) = A === B
-- /Source
def TomlEgalIdentityCorrect : Prop :=
  ∀ (W L : Type) (core : JuliaLean.base.boot.CoreOps W L) (left right : GenericValue L),
    tomlEgalIdentity { core with same := fun _ _ => true } left right = true ∧
    tomlEgalIdentity { core with same := fun _ _ => false } left right = false ∧
    ∀ otherCore : JuliaLean.base.boot.CoreOps W L,
      otherCore.same left right = core.same left right →
      tomlEgalIdentity otherCore left right = tomlEgalIdentity core left right

/-- Protected observations of each selected call and Core iterator-field
read. Native length tags are retained, and arbitrary membership/negation
results remain visible. Before/after worlds include failure effects.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
inductive TomlDictEvent (W L : Type) where
  | length (value : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (TomlLengthValue L)) (after : W)
  | first (iterator : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (Option (GenericValue L))) (after : W)
  | next (iterator state : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (Option (GenericValue L))) (after : W)
  | field (value index : GenericValue L) (before : W)
      (outcome : Except (GenericValue L) (GenericValue L)) (after : W)
  | member (pair dictionary : GenericValue L) (comparator : TomlComparator) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (DispatchValue (GenericValue L))) (after : W)
  | notOther (value : GenericValue L) (before : W)
      (outcome : Except (DispatchError (GenericValue L)) (DispatchValue (GenericValue L))) (after : W)

/-- Instrument every open dictionary operation without changing its
result/error/world. Core field reads are observed through the installed
primitive adapter; pure isa, selectors and TypeError fields retain their
original representation. Unused fields of otherCore stay arbitrary.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def traceTomlDict {W L : Type} (ops : TomlEgalOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (TomlDictEvent W L)) L) :
    TomlEgalOps (W × List (TomlDictEvent W L)) L where
  core := { otherCore with
    toLeafOps := ops.core.toLeafOps
    isa := ops.core.isa
    core := ops.core.core
    obj := ops.core.obj
    str := ops.core.str
    int := ops.core.int
    getfield := fun value index => recordSortCoreStep (.field value index) (ops.core.getfield value index) }
  idDictType := ops.idDictType
  iterateFirst := fun iterator => recordPackageStep (.first iterator) (ops.iterateFirst iterator)
  iterateNext := fun iterator state => recordPackageStep (.next iterator state) (ops.iterateNext iterator state)
  length := fun value => recordPackageStep (.length value) (ops.length value)
  member := fun pair dictionary comparator =>
    recordPackageStep (.member pair dictionary comparator) (ops.member pair dictionary comparator)
  notOther := fun value => recordPackageStep (.notOther value) (ops.notOther value)

/-- Every listed observation must actually arise from its named primitive
or selected callee at the recorded world. This is an observation relation,
not an assumption that any callee obeys a semantic correctness law.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def TomlDictEventsRealized {W L : Type} (ops : TomlEgalOps W L)
    (events : List (TomlDictEvent W L)) : Prop :=
  ∀ event, event ∈ events →
    match event with
    | .length value before outcome after => observe (ops.length value) before = some (outcome, after)
    | .first iterator before outcome after => observe (ops.iterateFirst iterator) before = some (outcome, after)
    | .next iterator state before outcome after => observe (ops.iterateNext iterator state) before = some (outcome, after)
    | .field value index before outcome after =>
        ops.core.getfield value index before = some (match outcome with
          | .ok result => .ok (result, after)
          | .error error => .error (error, after))
    | .member pair dictionary comparator before outcome after =>
        observe (ops.member pair dictionary comparator) before = some (outcome, after)
    | .notOther value before outcome after => observe (ops.notOther value) before = some (outcome, after)

/-- The negated guard uses a concrete Boolean complement for native Bool.
An arbitrary other value reaches exactly one selected ! call; its errors pass
through, a native Bool is consumed, and a non-Bool raises at the condition.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def TomlNegationTrace {W L : Type} (input : DispatchValue (GenericValue L)) (world : W)
    (result : Except (DispatchError (GenericValue L)) Bool) (finalWorld : W)
    (events : List (TomlDictEvent W L)) : Prop :=
  match input with
  | .bool true => events = [] ∧ result = .ok false ∧ finalWorld = world
  | .bool false => events = [] ∧ result = .ok true ∧ finalWorld = world
  | .other value =>
      ∃ outcome,
        events = [.notOther value world outcome finalWorld] ∧
        match outcome with
        | .error error => result = .error error
        | .ok (.bool flag) => result = .ok flag
        | .ok (.other _) => result = .error .typeError

/-- An iteration prefix reads value before state and passes the yielded
value unchanged to in with the original right dictionary and exact comparator.
This builds only a specification event list, not a model computation.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def TomlDictItemPrefix {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (iteration pair state right : GenericValue L) (world pairWorld stateWorld : W)
    (outcome : Except (DispatchError (GenericValue L)) (DispatchValue (GenericValue L)))
    (memberWorld : W) : List (TomlDictEvent W L) :=
  [.field iteration (JuliaLean.base.boot.intV core (JInt.lit .i64 1)) world (.ok pair) pairWorld,
   .field iteration (JuliaLean.base.boot.intV core (JInt.lit .i64 2)) pairWorld (.ok state) stateWorld,
   .member pair right .tomlEgal stateWorld outcome memberWorld]

/-- An independent finite trace language for the dictionary loop. It
allows no reads after an error, no iterator advance after rejection, and no
replacement of a supplied state or yielded pair. The recursive constructor
requires one real iterate-next event before the next iteration. There is no
fuel or finite-container premise.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
inductive TomlDictLoopTrace {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (left right : GenericValue L) : Option (GenericValue L) → W →
    Except (DispatchError (GenericValue L)) Bool → W → List (TomlDictEvent W L) → Prop where
  | empty (world : W) : TomlDictLoopTrace core left right none world (.ok true) world []
  | valueError (iteration error : GenericValue L) (world finalWorld : W) :
      TomlDictLoopTrace core left right (some iteration) world (.error (.other error)) finalWorld
        [.field iteration (JuliaLean.base.boot.intV core (JInt.lit .i64 1)) world (.error error) finalWorld]
  | stateError (iteration pair error : GenericValue L) (world pairWorld finalWorld : W) :
      TomlDictLoopTrace core left right (some iteration) world (.error (.other error)) finalWorld
        [.field iteration (JuliaLean.base.boot.intV core (JInt.lit .i64 1)) world (.ok pair) pairWorld,
         .field iteration (JuliaLean.base.boot.intV core (JInt.lit .i64 2)) pairWorld (.error error) finalWorld]
  | memberError (iteration pair state : GenericValue L)
      (world pairWorld stateWorld finalWorld : W) (error : DispatchError (GenericValue L)) :
      TomlDictLoopTrace core left right (some iteration) world (.error error) finalWorld
        (TomlDictItemPrefix core iteration pair state right world pairWorld stateWorld (.error error) finalWorld)
  | negationError (iteration pair state : GenericValue L)
      (world pairWorld stateWorld memberWorld finalWorld : W)
      (member : DispatchValue (GenericValue L)) (error : DispatchError (GenericValue L))
      (negEvents : List (TomlDictEvent W L))
      (negation : TomlNegationTrace member memberWorld (.error error) finalWorld negEvents) :
      TomlDictLoopTrace core left right (some iteration) world (.error error) finalWorld
        (TomlDictItemPrefix core iteration pair state right world pairWorld stateWorld (.ok member) memberWorld ++ negEvents)
  | rejected (iteration pair state : GenericValue L)
      (world pairWorld stateWorld memberWorld finalWorld : W)
      (member : DispatchValue (GenericValue L)) (negEvents : List (TomlDictEvent W L))
      (negation : TomlNegationTrace member memberWorld (.ok true) finalWorld negEvents) :
      TomlDictLoopTrace core left right (some iteration) world (.ok false) finalWorld
        (TomlDictItemPrefix core iteration pair state right world pairWorld stateWorld (.ok member) memberWorld ++ negEvents)
  | nextError (iteration pair state : GenericValue L)
      (world pairWorld stateWorld memberWorld negWorld finalWorld : W)
      (member : DispatchValue (GenericValue L)) (error : DispatchError (GenericValue L))
      (negEvents : List (TomlDictEvent W L))
      (negation : TomlNegationTrace member memberWorld (.ok false) negWorld negEvents) :
      TomlDictLoopTrace core left right (some iteration) world (.error error) finalWorld
        (TomlDictItemPrefix core iteration pair state right world pairWorld stateWorld (.ok member) memberWorld ++
          negEvents ++ [.next left state negWorld (.error error) finalWorld])
  | advance (iteration pair state : GenericValue L)
      (world pairWorld stateWorld memberWorld negWorld nextWorld finalWorld : W)
      (member : DispatchValue (GenericValue L)) (next : Option (GenericValue L))
      (result : Except (DispatchError (GenericValue L)) Bool)
      (negEvents rest : List (TomlDictEvent W L))
      (negation : TomlNegationTrace member memberWorld (.ok false) negWorld negEvents)
      (tail : TomlDictLoopTrace core left right next nextWorld result finalWorld rest) :
      TomlDictLoopTrace core left right (some iteration) world result finalWorld
        (TomlDictItemPrefix core iteration pair state right world pairWorld stateWorld (.ok member) memberWorld ++
          negEvents ++ [.next left state negWorld (.ok next) nextWorld] ++ rest)

/-- Independently specified native Int assertion failure: the exact
TypeError fields retain the offending value and expected Int64 type. This
relation does not invoke the model assertion helper or Core typeassert.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def IsTomlIntAssertionError {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (value : GenericValue L) (result : Except (DispatchError (GenericValue L)) Bool) : Prop :=
  result = .error (.other (.leaf (core.obj
    (.typeError (.symbol "typeassert") (.leaf (core.str "")) (.leaf (core.core "Int64")) value))))

/-- Both lengths are observed left to right and asserted without
conversion. A failed first assertion prevents the right length call. Native
values are compared mathematically in this property, without a positivity
premise, and only equal native lengths reach the iterator.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def TomlDictLengthsTrace {W L : Type} (core : JuliaLean.base.boot.CoreOps W L)
    (left right : GenericValue L) (world : W)
    (result : Except (DispatchError (GenericValue L)) Bool) (finalWorld : W)
    (events : List (TomlDictEvent W L)) : Prop :=
  (∃ error, events = [.length left world (.error error) finalWorld] ∧ result = .error error) ∨
  (∃ value, events = [.length left world (.ok (.notInt value)) finalWorld] ∧
    IsTomlIntAssertionError core value result) ∨
  (∃ leftLength leftWorld rightOutcome rightWorld suffix,
    events = [.length left world (.ok (.nativeInt leftLength)) leftWorld,
      .length right leftWorld rightOutcome rightWorld] ++ suffix ∧
    match rightOutcome with
    | .error error => suffix = [] ∧ result = .error error ∧ finalWorld = rightWorld
    | .ok (.notInt value) => suffix = [] ∧ IsTomlIntAssertionError core value result ∧ finalWorld = rightWorld
    | .ok (.nativeInt rightLength) =>
        (leftLength.val ≠ rightLength.val ∧ suffix = [] ∧ result = .ok false ∧ finalWorld = rightWorld) ∨
        (leftLength.val = rightLength.val ∧ ∃ firstOutcome firstWorld rest,
          suffix = [.first left rightWorld firstOutcome firstWorld] ++ rest ∧
          match firstOutcome with
          | .error error => rest = [] ∧ result = .error error ∧ finalWorld = firstWorld
          | .ok current => TomlDictLoopTrace core left right current firstWorld result finalWorld rest))

/-- The independent method trace begins with the native IdDict distinction.
Different kinds return false without any selected call; matching kinds enter
the length and iteration protocol. Native isa values are used directly.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def TomlDictTrace {W L : Type} (ops : TomlEgalOps W L)
    (left right : GenericValue L) (world : W)
    (result : Except (DispatchError (GenericValue L)) Bool) (finalWorld : W)
    (events : List (TomlDictEvent W L)) : Prop :=
  (ops.core.isa left ops.idDictType ≠ ops.core.isa right ops.idDictType ∧
    events = [] ∧ result = .ok false ∧ finalWorld = world) ∨
  (ops.core.isa left ops.idDictType = ops.core.isa right ops.idDictType ∧
    TomlDictLengthsTrace ops.core left right world result finalWorld events)

/-- For every dictionary subtype and arbitrary selected callees, terminal
observations are exactly the realized finite traces admitted by the independent
protocol. This checks all errors, native assertions, malformed iteration
results, state forwarding, comparator identity, custom ! behavior and early
exit. The divergence equivalence requires the absence of any realized finite
trace, so even infinite custom iteration is included without a fuel bound or
callee-termination assumption. No model body computes the expected result.
Julia documentation: doc/src/manual/interfaces.md:29-54;
doc/src/manual/control-flow.md:182-193.
Julia source: base/loading.jl:4876-4883. -/
-- Source: base/loading.jl:4876-4883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function toml_egal(A::AbstractDict, B::AbstractDict)
--     isa(A,IdDict) != isa(B,IdDict) && return false
--     length(A)::Int != length(B)::Int && return false
--     for pair in A
--         !in(pair, B, toml_egal) && return false
--     end
--     return true
-- end
-- /Source
def TomlEgalDictCorrect : Prop :=
  ∀ (W L : Type) (ops : TomlEgalOps W L)
      (otherCore : JuliaLean.base.boot.CoreOps (W × List (TomlDictEvent W L)) L)
      (left right : GenericValue L) (world : W),
    (∀ result finalWorld events,
      observe (tomlEgalDict (traceTomlDict ops otherCore) left right) (world, []) =
          some (result, (finalWorld, events)) ↔
        TomlDictTrace ops left right world result finalWorld events ∧
        TomlDictEventsRealized ops events) ∧
    (observe (tomlEgalDict ops left right) world = none ↔
      ¬ ∃ result finalWorld events,
        TomlDictTrace ops left right world result finalWorld events ∧
        TomlDictEventsRealized ops events)



/-- Protected observations separate real Base expansion leaves, one
selected custom expansion, and the final selected constructor. Complete
runtime values and mutation worlds are retained in every observation.
Julia source: base/loading.jl:5199. -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
inductive CompilerChiEvent (W L : Type) where
  | expansion (event : CompilerPathEvent W L)
  | custom (tup : CompilerPathValue L) (before : W)
      (outcome : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L)) (after : W)
  | construct (expanded : CompilerPathValue L) (before : W)
      (outcome : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L)) (after : W)

/-- Protect every actual Base expansion leaf in the wrapper's log.
This instruments the existing body rather than supplying an expansion callback.
The pure native tuple representation is unchanged, including input embedding
and prefix construction; unused Core fields cannot affect the execution.
Julia source: base/loading.jl:5199 (the expansion call).
Julia source: base/loading.jl:5196-5198 (the called Base body). -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
-- Source: base/loading.jl:5196-5198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expand_compiler_path(tup)
--     (tup[1], joinpath(Sys.BINDIR, DATAROOTDIR, tup[2]), tup[3:end]...)
-- end
-- /Source
def traceCompilerChiExpansion {W L : Type} (ops : ExpandCompilerPathOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps
      (W × List (CompilerChiEvent W L)) (CompilerPathLeaf L)) :
    ExpandCompilerPathOps (W × List (CompilerChiEvent W L)) L where
  core := { otherCore with
    tuple := ops.core.tuple
    applyIterate := fun iteration arguments =>
      recordSortCoreStep
        (fun before outcome after => CompilerChiEvent.expansion
          ⟨.splat iteration arguments, before, outcome.mapError DispatchError.other, after⟩)
        (ops.core.applyIterate iteration arguments) }
  bindir := ops.bindir
  datarootdir := ops.datarootdir
  getindexScalar := fun tup index =>
    recordPackageStep (fun before outcome after => CompilerChiEvent.expansion
      ⟨.scalar tup index, before, outcome, after⟩) (ops.getindexScalar tup index)
  joinpath := fun bindir datarootdir second =>
    recordPackageStep (fun before outcome after => CompilerChiEvent.expansion
      ⟨.joinpath bindir datarootdir second, before, outcome, after⟩)
      (ops.joinpath bindir datarootdir second)
  lastindex := fun tup =>
    recordPackageStep (fun before outcome after => CompilerChiEvent.expansion
      ⟨.lastindex tup, before, outcome, after⟩) (ops.lastindex tup)
  colon := fun first last =>
    recordPackageStep (fun before outcome after => CompilerChiEvent.expansion
      ⟨.colon first last, before, outcome, after⟩) (ops.colon first last)
  getindexSlice := fun tup range =>
    recordPackageStep (fun before outcome after => CompilerChiEvent.expansion
      ⟨.slice tup range, before, outcome, after⟩) (ops.getindexSlice tup range)

/-- Preserve dispatch metadata and protect both open-call outcomes.
Selected code can mutate its own world but cannot forge this separate log.
Julia source: base/loading.jl:5199. -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
def traceCompilerChi {W L : Type} (ops : CompilerChiOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps
      (W × List (CompilerChiEvent W L)) (CompilerPathLeaf L)) :
    CompilerChiOps (W × List (CompilerChiEvent W L)) L where
  baseExpansion := traceCompilerChiExpansion ops.baseExpansion otherCore
  selection := ops.selection
  customExpansion := fun tup =>
    recordPackageStep (.custom tup) (ops.customExpansion tup)
  constructHeader := fun expanded =>
    recordPackageStep (.construct expanded) (ops.constructHeader expanded)

/-- Independent continuation protocol: expansion failure prevents
construction, while expansion success causes exactly one call with the same
runtime value. Both constructor success and failure are returned with their
actual final worlds; no header result type or shape is asserted.
Julia source: base/loading.jl:5199. -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
def CompilerChiContinuation {W L : Type}
    (expansionOutcome result : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L))
    (middle finalWorld : W) (events : List (CompilerChiEvent W L)) : Prop :=
  match expansionOutcome with
  | .error error => events = [] ∧ result = .error error ∧ finalWorld = middle
  | .ok expanded => events = [.construct expanded middle result finalWorld]

/-- The complete terminating protocol uses the already independent
seven-operation expansion invariant on Base selection. Custom selection has
one unrestricted expansion observation. Their common continuation preserves
the exact returned value, call order and failure worlds.
Julia source: base/loading.jl:5199. -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
def CompilerChiTerminal {W L : Type} (ops : CompilerChiOps W L)
    (tup : CompilerPathValue L) (world : W)
    (result : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L))
    (finalWorld : W) (events : List (CompilerChiEvent W L)) : Prop :=
  match ops.selection tup with
  | .base =>
      ∃ («prefix» : List (CompilerPathEvent W L))
          (expansionOutcome : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L))
          (middle : W) (suffix : List (CompilerChiEvent W L)),
        events = «prefix».map CompilerChiEvent.expansion ++ suffix ∧
        CompilerPathTerminal ops.baseExpansion tup world expansionOutcome middle «prefix» ∧
        CompilerChiContinuation expansionOutcome result middle finalWorld suffix
  | .custom =>
      ∃ (expansionOutcome : Except (DispatchError (CompilerPathValue L)) (CompilerPathValue L))
          (middle : W) (suffix : List (CompilerChiEvent W L)),
        events = [.custom tup world expansionOutcome middle] ++ suffix ∧
        CompilerChiContinuation expansionOutcome result middle finalWorld suffix

/-- Reachability of a successful Base expansion is stated using actual
leaf observations, the independent source-order protocol and native-splat
terminal result. It does not invoke expandCompilerPath as an oracle and
does not assume any indexing, joinpath, iteration or constructor law.
Julia source: base/loading.jl:5199 (the expansion dependency). -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
def CompilerChiBaseProduces {W L : Type} (ops : ExpandCompilerPathOps W L)
    (tup : CompilerPathValue L) (world : W) (expanded : CompilerPathValue L)
    (middle : W) : Prop :=
  ∃ events : List (CompilerPathEvent W L),
    CompilerPathTerminal ops tup world (.ok expanded) middle events ∧
    ∀ event, event ∈ events →
      observe (compilerPathCallAction ops event.call) event.before = some (event.outcome, event.after)

/-- Exactly the selected expansion's actual successful output may
reach the outer constructor. The Base alternative remains grounded in its
real leaves; the custom alternative retains all arbitrary selected outcomes.
Julia source: base/loading.jl:5199. -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
def CompilerChiExpansionProduces {W L : Type} (ops : CompilerChiOps W L)
    (tup : CompilerPathValue L) (world : W) (expanded : CompilerPathValue L)
    (middle : W) : Prop :=
  match ops.selection tup with
  | .base => CompilerChiBaseProduces ops.baseExpansion tup world expanded middle
  | .custom => observe (ops.customExpansion tup) world = some (.ok expanded, middle)

/-- Divergence occurs only in a reached operation: the chosen
expansion or the selected constructor after an actual successful expansion.
Earlier errors cannot be mistaken for reaching a later divergent call.
Julia source: base/loading.jl:5199. -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
def CompilerChiDivergence {W L : Type} (ops : CompilerChiOps W L)
    (tup : CompilerPathValue L) (world : W) : Prop :=
  (match ops.selection tup with
   | .base => CompilerPathDivergence ops.baseExpansion tup world
   | .custom => observe (ops.customExpansion tup) world = none) ∨
  ∃ expanded middle,
    CompilerChiExpansionProduces ops tup world expanded middle ∧
    observe (ops.constructHeader expanded) middle = none

/-- Full Tuple-domain expansion-before-construction invariant. Arity
is only bounded by the installed native representation; no five-field header
restriction excludes empty, short, long or heterogeneous inputs. Base
selection runs the source expansion protocol, while custom selection keeps
its arbitrary result. Construction receives that exact runtime value once,
and every result, exception, failure world and reached divergence survives.
Protected trace erasure preserves the original execution. The registered
property covers compilerChi, selectedCompilerChiExpansion and the reused
expandCompilerPath dependency without any callee-correctness assumptions.
Julia source: base/loading.jl:5199.
Julia documentation: doc/src/manual/types.md:964-1000;
doc/src/devdocs/types.md:250-318. -/
-- Source: base/loading.jl:5199-5199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compiler_chi(tup::Tuple) = CacheHeaderIncludes(expand_compiler_path(tup))
-- /Source
def CompilerChiCorrect : Prop :=
  ∀ (W L : Type) (ops : CompilerChiOps W L)
      (otherCore : JuliaLean.base.boot.CoreOps
        (W × List (CompilerChiEvent W L)) (CompilerPathLeaf L))
      (tup : CompilerChiTuple L) (world : W),
    let value : CompilerPathValue L := .leaf (ops.baseExpansion.core.tuple tup.values)
    let plain := observe (compilerChi ops tup) world
    let traced := observe (compilerChi (traceCompilerChi ops otherCore) tup) (world, [])
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result finalWorld events, traced = some (result, (finalWorld, events)) →
      CompilerChiTerminal ops value world result finalWorld events) ∧
    (plain = none ↔ CompilerChiDivergence ops value world)


open JuliaLean.base.loading (World LOps LM LErr)

/-- Observe the existing loading effect carrier without altering its
exception representation or losing the world attached to a failure.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def observePrecompilable {E W A : Type}
    (action : ExceptT (LErr E) (StateT W Option) A) (world : W) :
    Option (Except (LErr E) A × W) :=
  StateT.run (ExceptT.run action) world

/-- Distinguish runtime type-construction values, the native C Int32
result, and an arbitrary custom method result. These are observation tags.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
inductive PrecompilableKind where
  | value
  | int32
  | returned

/-- Native C results retain their fixed-width carrier. Type construction
and arbitrary custom returns preserve their entire runtime value domains.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableResponse (L : Type) : PrecompilableKind → Type
  | .value => PrecompilableValue L
  | .int32 => JInt .i32
  | .returned => DispatchValue (PrecompilableValue L)

/-- Requests retain exact native type parameters, splat grouping and
function identities. Separate final Base and custom requests make selection
observable. No request stands for Typeof or the entire wrapper body.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
inductive PrecompilableRequest (L : Type) : PrecompilableKind → Type where
  | customTypeof (function : PrecompilableValue L) : PrecompilableRequest L .value
  | typeApplication (typeConstructor : PrecompilableValue L)
      (parameters : List (PrecompilableValue L)) : PrecompilableRequest L .value
  | splat (iteration : PrecompilableValue L)
      (arguments : List (PrecompilableValue L)) : PrecompilableRequest L .value
  | query (signature : PrecompilableValue L) : PrecompilableRequest L .int32
  | custom (signature : PrecompilableValue L) : PrecompilableRequest L .returned

/-- One actual primitive or selected method observation includes its
complete result or exception and both worlds. Witnesses are subsequently
checked against actual observations, not accepted as correctness premises.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
structure PrecompilableEvent (W L : Type) where
  kind : PrecompilableKind
  request : PrecompilableRequest L kind
  before : W
  outcome : Except (LErr (PrecompilableValue L)) (PrecompilableResponse L kind)
  after : W

/-- Read a successful earlier runtime value without manufacturing a
default for an absent, failed or differently typed observation.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def precompilableValueAt {W L : Type}
    (events : List (PrecompilableEvent W L)) (slot : Nat) : Option (PrecompilableValue L) :=
  match events[slot]? with
  | some ⟨.value, _, _, .ok value, _⟩ => some value
  | _ => none

/-- Custom Core.Typeof contributes an effectful observation. Selected
Base does so only for a type-valued argument; its ordinary typeof branch is
pure. This is source dispatch metadata, not a selected-callee result law.
Julia source: base/loading.jl:5207-5213; base/boot.jl:297-309. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def precompilableHasTypeofCall {W L : Type}
    (core : JuliaLean.base.boot.CoreOps W (PrecompilableLeaf L))
    (typeOfSelection : PrecompilableValue L → PrecompilableSelection)
    (function : PrecompilableValue L) : Bool :=
  match typeOfSelection function with
  | .base => core.isa function (JuliaLean.base.boot.coreV core "Type")
  | .custom => true

/-- Independent source-slot and argument constraints. Selected custom Core.Typeof contributes an unrestricted effectful value.
Selected Base on a type value requires one Type or TypeEgal application;
selected Base on any other value contributes its native typeof result. The following splat preserves
every original tuple field, including invalid parameters. The final request
must use the preceding signature and its actual Base/custom selection.
Every causal reference is strictly earlier than its request slot.
Julia documentation: base/boot.jl:297-309.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableRequestAllowed {W L : Type}
    (core : JuliaLean.base.boot.CoreOps W (PrecompilableLeaf L))
    (typeOfSelection : PrecompilableValue L → PrecompilableSelection)
    (selection : PrecompilableValue L → PrecompilableSelection)
    (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
    (events : List (PrecompilableEvent W L)) (slot : Nat)
    {kind : PrecompilableKind} (request : PrecompilableRequest L kind) : Prop :=
  match request with
  | .customTypeof actualFunction =>
      typeOfSelection function = .custom ∧ slot = 0 ∧ actualFunction = function
  | .typeApplication typeConstructor parameters =>
      typeOfSelection function = .base ∧
      core.isa function (JuliaLean.base.boot.coreV core "Type") = true ∧
      slot = 0 ∧ parameters = [function] ∧
      typeConstructor = JuliaLean.base.boot.coreV core
        (if core.hasFreeTypevars function then "Type" else "TypeEgal")
  | .splat iteration arguments =>
      slot = (if precompilableHasTypeofCall core typeOfSelection function then 1 else 0) ∧
      iteration = .leaf (.inl PrecompilableBuiltin.baseIterate) ∧
      ∃ functionType,
        ((precompilableHasTypeofCall core typeOfSelection function = true ∧
            precompilableValueAt events 0 = some functionType) ∨
         (precompilableHasTypeofCall core typeOfSelection function = false ∧
            functionType = .leaf (core.typeOf function))) ∧
        arguments = [.leaf (.inl PrecompilableBuiltin.coreApplyType),
          .leaf (core.tuple [JuliaLean.base.boot.coreV core "Tuple", functionType]),
          .leaf (core.tuple argtypes.values)]
  | .query signature =>
      slot = (if precompilableHasTypeofCall core typeOfSelection function then 2 else 1) ∧
      precompilableValueAt events (slot - 1) = some signature ∧ selection signature = .base
  | .custom signature =>
      slot = (if precompilableHasTypeofCall core typeOfSelection function then 2 else 1) ∧
      precompilableValueAt events (slot - 1) = some signature ∧ selection signature = .custom

/-- World continuity retains mutations before all errors. An empty
prefix has the same incoming and outgoing world.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
inductive PrecompilableWorldChain {W L : Type} :
    W → W → List (PrecompilableEvent W L) → Prop where
  | empty (world : W) : PrecompilableWorldChain (L := L) world world []
  | step (event : PrecompilableEvent W L) (finalWorld : W)
      (events : List (PrecompilableEvent W L))
      (following : PrecompilableWorldChain event.after finalWorld events) :
      PrecompilableWorldChain event.before finalWorld (event :: events)

/-- Each event occupies its unique allowed source slot. No operation
can appear after the selected unary query or custom method.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableCallOrder {W L : Type}
    (core : JuliaLean.base.boot.CoreOps W (PrecompilableLeaf L))
    (typeOfSelection : PrecompilableValue L → PrecompilableSelection)
    (selection : PrecompilableValue L → PrecompilableSelection)
    (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
    (events : List (PrecompilableEvent W L)) : Prop :=
  ∀ slot event, events[slot]? = some event →
    PrecompilableRequestAllowed core typeOfSelection selection function argtypes events slot event.request

/-- Only a successful event may precede another source operation.
Its result kind and slot are checked independently by the request protocol.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableSucceeded {W L : Type} (event : PrecompilableEvent W L) : Prop :=
  match event.outcome with
  | .ok _ => True
  | .error _ => False

/-- The terminal outcome is an unchanged exception, the mathematical
nonzero classification of the final signed Int32 C result, or the exact
arbitrary custom return. A successful type construction cannot terminate
the wrapper early. No Bool coercion is imposed on a custom result.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableLastResult {W L : Type} (event : PrecompilableEvent W L)
    (result : Except (LErr (PrecompilableValue L)) (DispatchValue (PrecompilableValue L))) : Prop :=
  match event with
  | ⟨_, _, _, .error error, _⟩ => result = .error error
  | ⟨.int32, _, _, .ok code, _⟩ =>
      ∃ value, result = .ok (.bool value) ∧ (value = true ↔ code.val ≠ 0)
  | ⟨.returned, _, _, .ok value, _⟩ => result = .ok value
  | _ => False

/-- An independent finite protocol requires a successful prefix, exact
source arguments and continuous worlds before its one legal terminal event.
All invalid tuple fields and native failures remain in the input domain.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableTerminal {W L : Type}
    (core : JuliaLean.base.boot.CoreOps W (PrecompilableLeaf L))
    (typeOfSelection : PrecompilableValue L → PrecompilableSelection)
    (selection : PrecompilableValue L → PrecompilableSelection)
    (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
    (world : W)
    (result : Except (LErr (PrecompilableValue L)) (DispatchValue (PrecompilableValue L)))
    (finalWorld : W) (events : List (PrecompilableEvent W L)) : Prop :=
  events.length ≤ 3 ∧ PrecompilableCallOrder core typeOfSelection selection function argtypes events ∧
  PrecompilableWorldChain world finalWorld events ∧
  ∃ («prefix» : List (PrecompilableEvent W L)) (last : PrecompilableEvent W L),
    events = «prefix» ++ [last] ∧
    (∀ event, event ∈ «prefix» → PrecompilableSucceeded event) ∧
    PrecompilableLastResult last result

/-- Interpret only a single recorded primitive or selected request.
This is not an expected-result function for the wrapper or its signature
helper. It uses the existing Core adapter and typed C interface unchanged.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def precompilableRequestAction {X Y D CI CF Version L : Type}
    (o : LOps X Y (PrecompilableValue L) D CI CF Version)
    (core : JuliaLean.base.boot.CoreOps (World X D CI CF) (PrecompilableLeaf L))
    (typeOfOps : PrecompilableTypeofOps o)
    (dispatch : PrecompilableDispatch o)
    {kind : PrecompilableKind} (request : PrecompilableRequest L kind) :
    LM o (PrecompilableResponse L kind) :=
  match request with
  | .customTypeof function => typeOfOps.custom function
  | .typeApplication typeConstructor parameters =>
      liftPrecompilableCore o (core.applyType typeConstructor parameters)
  | .splat iteration arguments =>
      liftPrecompilableCore o (core.applyIterate iteration arguments)
  | .query signature => dispatch.compiler.isCompilable signature
  | .custom signature => dispatch.custom signature

/-- Verify each event against its actual primitive observation. An
existential trace cannot invent results, turn a failure into success, or
forge a before/after world; all call implementations are universally quantified.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableActualEvents {X Y D CI CF Version L : Type}
    (o : LOps X Y (PrecompilableValue L) D CI CF Version)
    (core : JuliaLean.base.boot.CoreOps (World X D CI CF) (PrecompilableLeaf L))
    (typeOfOps : PrecompilableTypeofOps o)
    (dispatch : PrecompilableDispatch o)
    (events : List (PrecompilableEvent (World X D CI CF) L)) : Prop :=
  ∀ event, event ∈ events →
    observePrecompilable (precompilableRequestAction o core typeOfOps dispatch event.request) event.before =
      some (event.outcome, event.after)

/-- A reached prefix contains only actual successful earlier calls.
A later divergence cannot be reached after an earlier error. The length
excludes any already-completed final query/custom call.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableReachedPrefix {X Y D CI CF Version L : Type}
    (o : LOps X Y (PrecompilableValue L) D CI CF Version)
    (core : JuliaLean.base.boot.CoreOps (World X D CI CF) (PrecompilableLeaf L))
    (typeOfOps : PrecompilableTypeofOps o)
    (dispatch : PrecompilableDispatch o)
    (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
    (world middle : World X D CI CF)
    (events : List (PrecompilableEvent (World X D CI CF) L)) : Prop :=
  events.length < (if precompilableHasTypeofCall core typeOfOps.selection function then 3 else 2) ∧
  PrecompilableCallOrder core typeOfOps.selection dispatch.selection function argtypes events ∧
  PrecompilableWorldChain world middle events ∧
  (∀ event, event ∈ events → PrecompilableSucceeded event) ∧
  PrecompilableActualEvents o core typeOfOps dispatch events

/-- Divergence originates in a genuinely reached native Typeof
application, type-application splat, C query or selected custom method.
Earlier worlds and values satisfy the same independent source protocol.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableDivergence {X Y D CI CF Version L : Type}
    (o : LOps X Y (PrecompilableValue L) D CI CF Version)
    (core : JuliaLean.base.boot.CoreOps (World X D CI CF) (PrecompilableLeaf L))
    (typeOfOps : PrecompilableTypeofOps o)
    (dispatch : PrecompilableDispatch o)
    (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
    (world : World X D CI CF) : Prop :=
  ∃ («prefix» : List (PrecompilableEvent (World X D CI CF) L)) (middle : World X D CI CF)
      (kind : PrecompilableKind) (request : PrecompilableRequest L kind),
    PrecompilableReachedPrefix o core typeOfOps dispatch function argtypes world middle «prefix» ∧
    PrecompilableRequestAllowed core typeOfOps.selection dispatch.selection function argtypes «prefix» «prefix».length request ∧
    observePrecompilable (precompilableRequestAction o core typeOfOps dispatch request) middle = none

/-- Independent raw-Core observation law for the representation adapter.
The expected side inspects only action world, not another invocation of the
adapter. This detects changes to any successful value, exact exception
payload, failure world or divergence and is conjoined in all public properties.
Julia source: base/loading.jl:5207-5213; base/boot.jl:297-309. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def PrecompilableCoreAdapterCorrect : Prop :=
  ∀ (X Y D CI CF Version L A : Type)
      (o : LOps X Y (PrecompilableValue L) D CI CF Version)
      (action : JuliaLean.base.boot.CoreM (World X D CI CF) (PrecompilableLeaf L) A)
      (world : World X D CI CF),
    match action world with
    | none => observePrecompilable (liftPrecompilableCore o action) world = none
    | some (.ok (value, finalWorld)) =>
        observePrecompilable (liftPrecompilableCore o action) world = some (.ok value, finalWorld)
    | some (.error (error, finalWorld)) =>
        observePrecompilable (liftPrecompilableCore o action) world =
          some (.error (.ext error), finalWorld)

/-- Full-domain source protocol over all bounded native argument tuples,
including invalid parameters/Varargs, all function/type values and all native
worlds. Core and compiler/custom operations have no correctness-law premise.
The independent event language fixes Typeof selection, exact splat identities,
grouping and field order, fail-fast errors/worlds, final dispatch and the native
nonzero result or unchanged custom return. Each witness is verified against
actual primitive observations; divergence has exactly a reached-call origin.
This covers the signature helper, the lossless Core adapter and actual reuse
of installed isprecompilable_type. Obsolete pure adapters are never consulted.
Julia source: base/loading.jl:5207-5213. -/
-- Source: base/loading.jl:5201-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isprecompilable(f, argtypes::Tuple{Vararg{Any}})
-- 
-- Check, as far as is possible without actually compiling, if the given
-- function `f` can be compiled for the argument tuple (of types) `argtypes`.
-- """
-- function isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     isprecompilable(Tuple{Core.Typeof(f), argtypes...})
-- end
-- 
-- function isprecompilable(@nospecialize(argt::Type))
--     ccall(:jl_is_compilable, Int32, (Any,), argt) != 0
-- end
-- /Source
def IsPrecompilableFunctionCorrect : Prop :=
  PrecompilableCoreAdapterCorrect ∧
  ∀ (X Y D CI CF Version L : Type)
      (o : LOps X Y (PrecompilableValue L) D CI CF Version)
      (core : JuliaLean.base.boot.CoreOps (World X D CI CF) (PrecompilableLeaf L))
      (typeOfOps : PrecompilableTypeofOps o)
      (dispatch : PrecompilableDispatch o)
      (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
      (world : World X D CI CF),
    (∀ result finalWorld,
      observePrecompilable (isPrecompilableFunction o core typeOfOps dispatch function argtypes) world =
        some (result, finalWorld) →
      ∃ events,
        PrecompilableTerminal core typeOfOps.selection dispatch.selection function argtypes world result finalWorld events ∧
        PrecompilableActualEvents o core typeOfOps dispatch events) ∧
    (observePrecompilable (isPrecompilableFunction o core typeOfOps dispatch function argtypes) world = none ↔
      PrecompilableDivergence o core typeOfOps dispatch function argtypes world)

/-- Reuse the independent native-signature event protocol with a final
selected unary precompile call. The witness compiler record is universally
quantified observation metadata: selection is always custom in this trace
encoding, so its C-query branch is unreachable and contributes no premise.
Actual event observations fix the final target to ops.unary. Every successful
return, exception and mutation world is preserved, and divergence has a
reached-call origin. No selected-precompile correctness law is assumed.
Julia source: base/loading.jl:5220-5222. -/
-- Source: base/loading.jl:5220-5222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(f), @nospecialize(argtypes::Tuple))
--     precompile(Tuple{Core.Typeof(f), argtypes...})
-- end
-- /Source
def PrecompileFunctionCorrect : Prop :=
  PrecompilableCoreAdapterCorrect ∧
  ∀ (X Y D CI CF Version L Method : Type)
      (o : LOps X Y (PrecompilableValue L) D CI CF Version)
      (core : JuliaLean.base.boot.CoreOps (World X D CI CF) (PrecompilableLeaf L))
      (typeOfOps : PrecompilableTypeofOps o)
      (witnessCompiler : PrecompilableCompilerOps o)
      (ops : PrecompileForwardOps o Method)
      (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
      (world : World X D CI CF),
    let observed : PrecompilableDispatch o :=
      { compiler := witnessCompiler, selection := fun _ => .custom, custom := ops.unary }
    (∀ result finalWorld,
      observePrecompilable (precompileFunction o core typeOfOps ops function argtypes) world =
        some (result, finalWorld) →
      ∃ events,
        PrecompilableTerminal core typeOfOps.selection observed.selection function argtypes world result finalWorld events ∧
        PrecompilableActualEvents o core typeOfOps observed events) ∧
    (observePrecompilable (precompileFunction o core typeOfOps ops function argtypes) world = none ↔
      PrecompilableDivergence o core typeOfOps observed function argtypes world)

/-- The same independent source protocol fixes the final selected
precompile call to the exact constructed signature and original Method.
Changing the Method, its ordering or either signature input is detectable
over arbitrary selected callees. The custom tag here denotes the open
selected-call observation; it does not exclude selection of a Base method.
The universally quantified witness compiler is unreachable observation
metadata, not a required law or a callee implementation supplied to the model.
Julia source: base/loading.jl:5244-5246. -/
-- Source: base/loading.jl:5244-5246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(f), @nospecialize(argtypes::Tuple), m::Method)
--     precompile(Tuple{Core.Typeof(f), argtypes...}, m)
-- end
-- /Source
def PrecompileFunctionMethodCorrect : Prop :=
  PrecompilableCoreAdapterCorrect ∧
  ∀ (X Y D CI CF Version L Method : Type)
      (o : LOps X Y (PrecompilableValue L) D CI CF Version)
      (core : JuliaLean.base.boot.CoreOps (World X D CI CF) (PrecompilableLeaf L))
      (typeOfOps : PrecompilableTypeofOps o)
      (witnessCompiler : PrecompilableCompilerOps o)
      (ops : PrecompileForwardOps o Method)
      (function : PrecompilableValue L) (argtypes : PrecompilableArguments L)
      (method : Method) (world : World X D CI CF),
    let observed : PrecompilableDispatch o :=
      { compiler := witnessCompiler, selection := fun _ => .custom,
        custom := fun signature => ops.withMethod signature method }
    (∀ result finalWorld,
      observePrecompilable (precompileFunctionMethod o core typeOfOps ops function argtypes method) world =
        some (result, finalWorld) →
      ∃ events,
        PrecompilableTerminal core typeOfOps.selection observed.selection function argtypes world result finalWorld events ∧
        PrecompilableActualEvents o core typeOfOps observed events) ∧
    (observePrecompilable (precompileFunctionMethod o core typeOfOps ops function argtypes method) world = none ↔
      PrecompilableDivergence o core typeOfOps observed function argtypes world)



/-- Protected requests distinguish installed Core field access from
selected calls and retain the exact function identity and argument list.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
inductive PrecompileMethodCall (L : Type) where
  | field (object selector : GenericValue L)
  | dispatch (function : PrecompileMethodFunction) (arguments : List (GenericValue L))

/-- Every completed operation retains its result or complete error,
plus the worlds before and after the operation. No pair/Bool result is imposed.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
structure PrecompileMethodEvent (W L : Type) where
  call : PrecompileMethodCall L
  before : W
  outcome : Except (DispatchError (GenericValue L)) (GenericValue L)
  after : W

/-- Protect all reached operations without changing their behavior.
Core field errors are embedded exactly as in the installed adapter. Integer
representations are retained, and every other Core field is unused. Selected
code can mutate W but has no access to the separately maintained event list.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def tracePrecompileMethod {W L : Type} (ops : PrecompileMethodOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (PrecompileMethodEvent W L)) L) :
    PrecompileMethodOps (W × List (PrecompileMethodEvent W L)) L where
  core := { otherCore with
    int := ops.core.int
    getfield := fun object selector =>
      recordSortCoreStep
        (fun before outcome after =>
          ⟨.field object selector, before, outcome.mapError DispatchError.other, after⟩)
        (ops.core.getfield object selector) }
  call := fun function arguments =>
    recordPackageStep (fun before outcome after =>
      ⟨.dispatch function arguments, before, outcome, after⟩) (ops.call function arguments)

/-- Only actual successful prior observations supply later arguments.
Absent observations and failures never produce fabricated default values.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def precompileMethodValueAt {W L : Type} (events : List (PrecompileMethodEvent W L))
    (index : Nat) : Option (GenericValue L) :=
  match events[index]? with
  | some event => match event.outcome with
    | .ok value => some value
    | .error _ => none
  | none => none

/-- Independent operand and order constraints for all nine operations.
The two indexed_iterate calls use native indices one/two, and only the first
result supplies a state. Specialization has the exact Compiler namespace tag
and original Method. The last call receives precisely its unrestricted result.
Julia source: base/loading.jl:5248-5252.
Julia documentation: doc/src/manual/functions.md:394-432. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def PrecompileMethodCallAllowed {W L : Type} (ops : PrecompileMethodOps W L)
    (argtype method : GenericValue L) (events : List (PrecompileMethodEvent W L))
    (slot : Nat) (call : PrecompileMethodCall L) : Prop :=
  let one : GenericValue L := .leaf (ops.core.int (JInt.lit .i64 1))
  let two : GenericValue L := .leaf (ops.core.int (JInt.lit .i64 2))
  match call with
  | .field object selector =>
      (slot = 0 ∧ object = method ∧ selector = .symbol "sig") ∨
      (slot = 3 ∧ precompileMethodValueAt events 2 = some object ∧ selector = one) ∨
      (slot = 4 ∧ precompileMethodValueAt events 2 = some object ∧ selector = two) ∨
      (slot = 6 ∧ precompileMethodValueAt events 5 = some object ∧ selector = one)
  | .dispatch function arguments =>
      match function with
      | .typeintersectEnv =>
          slot = 1 ∧ ∃ signature,
            precompileMethodValueAt events 0 = some signature ∧ arguments = [argtype, signature]
      | .indexedIterate =>
          (slot = 2 ∧ ∃ intersection,
            precompileMethodValueAt events 1 = some intersection ∧ arguments = [intersection, one]) ∨
          (slot = 5 ∧ ∃ intersection state,
            precompileMethodValueAt events 1 = some intersection ∧
            precompileMethodValueAt events 4 = some state ∧ arguments = [intersection, two, state])
      | .compilerSpecializeMethod =>
          slot = 7 ∧ ∃ atype sparams,
            precompileMethodValueAt events 3 = some atype ∧
            precompileMethodValueAt events 6 = some sparams ∧ arguments = [method, atype, sparams]
      | .precompile =>
          slot = 8 ∧ ∃ specialized,
            precompileMethodValueAt events 7 = some specialized ∧ arguments = [specialized]

/-- Event worlds connect in execution order even when a selected
method or a native projection fails. The relation itself performs no call.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
inductive PrecompileMethodWorldChain {W L : Type} :
    W → W → List (PrecompileMethodEvent W L) → Prop where
  | empty (world : W) : PrecompileMethodWorldChain (L := L) world world []
  | step (event : PrecompileMethodEvent W L) (finalWorld : W)
      (events : List (PrecompileMethodEvent W L))
      (following : PrecompileMethodWorldChain event.after finalWorld events) :
      PrecompileMethodWorldChain event.before finalWorld (event :: events)

/-- Every observed operation has its own source slot and operands.
No third iteration, extra state projection or extra precompile call is allowed.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def PrecompileMethodCallOrder {W L : Type} (ops : PrecompileMethodOps W L)
    (argtype method : GenericValue L) (events : List (PrecompileMethodEvent W L)) : Prop :=
  ∀ slot event, events[slot]? = some event →
    PrecompileMethodCallAllowed ops argtype method events slot event.call

/-- All completed predecessors succeeded. The last operation's entire
outcome is returned, with its actual final world. Success requires all nine
operations; any reached error stops at its original projection or call site.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def PrecompileMethodTerminal {W L : Type} (ops : PrecompileMethodOps W L)
    (argtype method : GenericValue L) (world : W)
    (result : Except (DispatchError (GenericValue L)) (GenericValue L))
    (finalWorld : W) (events : List (PrecompileMethodEvent W L)) : Prop :=
  events.length ≤ 9 ∧ PrecompileMethodCallOrder ops argtype method events ∧
  PrecompileMethodWorldChain world finalWorld events ∧
  ∃ («prefix» : List (PrecompileMethodEvent W L)) (last : PrecompileMethodEvent W L),
    events = «prefix» ++ [last] ∧
    (∀ event, event ∈ «prefix» → ∃ value, event.outcome = .ok value) ∧
    last.outcome = result ∧
    (∀ value, result = .ok value → events.length = 9)

/-- Observe one actual primitive/selected leaf for reachability.
This dispatches a single recorded request, not the enclosing Julia algorithm.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def precompileMethodCallAction {W L : Type} (ops : PrecompileMethodOps W L)
    (call : PrecompileMethodCall L) : GenericM W L (GenericValue L) :=
  match call with
  | .field object selector => liftCoreAction (ops.core.getfield object selector)
  | .dispatch function arguments => ops.call function arguments

/-- A reached prefix consists of actual successful earlier operations
with their original arguments and complete mutation history. No callee law
or assumption of well-formed intermediate results is used.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def PrecompileMethodReachedPrefix {W L : Type} (ops : PrecompileMethodOps W L)
    (argtype method : GenericValue L) (world middle : W)
    (events : List (PrecompileMethodEvent W L)) : Prop :=
  events.length < 9 ∧ PrecompileMethodCallOrder ops argtype method events ∧
  PrecompileMethodWorldChain world middle events ∧
  ∀ event, event ∈ events →
    (∃ value, event.outcome = .ok value) ∧
    observe (precompileMethodCallAction ops event.call) event.before = some (event.outcome, event.after)

/-- Divergence has an actually reached selected-call or primitive
origin. An earlier failure cannot reach a later divergent operation.
Julia source: base/loading.jl:5248-5252. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def PrecompileMethodDivergence {W L : Type} (ops : PrecompileMethodOps W L)
    (argtype method : GenericValue L) (world : W) : Prop :=
  ∃ («prefix» : List (PrecompileMethodEvent W L)) (middle : W) (call : PrecompileMethodCall L),
    PrecompileMethodReachedPrefix ops argtype method world middle «prefix» ∧
    PrecompileMethodCallAllowed ops argtype method «prefix» «prefix».length call ∧
    observe (precompileMethodCallAction ops call) middle = none

/-- Full-domain source-order and terminal protocol. The signature is
read from the original Method, each generic result is kept unrestricted, and
destructuring uses the exact indexed_iterate and Core projection sequence.
The exact Base.Compiler specialization identity and all three arguments are
protected; its returned value reaches selected precompile unchanged. Every
result, raw Core error, selected exception, failure world and reached divergence
survives without rollback or a fabricated Bool/MethodInstance restriction.
This property is falsifiable by altered arguments, namespace tags, ordering,
missing or repeated calls, coercions and lost failure effects. No correctness
law for any selected method or runtime primitive is assumed.
Julia source: base/loading.jl:5248-5252.
Julia documentation: doc/src/manual/functions.md:394-432. -/
-- Source: base/loading.jl:5248-5252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function precompile(@nospecialize(argt::Type), m::Method)
--     atype, sparams = typeintersect_env(argt, m.sig)
--     mi = Base.Compiler.specialize_method(m, atype, sparams)
--     return precompile(mi)
-- end
-- /Source
def PrecompileTypeMethodCorrect : Prop :=
  ∀ (W L : Type) (ops : PrecompileMethodOps W L)
      (otherCore : JuliaLean.base.boot.CoreOps (W × List (PrecompileMethodEvent W L)) L)
      (argtype method : GenericValue L) (world : W),
    let plain := observe (precompileTypeMethod ops argtype method) world
    let traced := observe (precompileTypeMethod (tracePrecompileMethod ops otherCore) argtype method)
      (world, [])
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result finalWorld events, traced = some (result, (finalWorld, events)) →
      PrecompileMethodTerminal ops argtype method world result finalWorld events) ∧
    (plain = none ↔ PrecompileMethodDivergence ops argtype method world)


end JuliaLean.Proofs.base.loading.Models2Group4

namespace JuliaLean.Proofs.base.loading
open JuliaLean.Registry

open JuliaLean JuliaLean.base.loading

-- Helpers for Models2Group4 ObservationM
private theorem observe_bind {E W α β : Type}
    (act : Models2Group4.ObservationM E W α)
    (f : α → Models2Group4.ObservationM E W β) (w : W) :
    Models2Group4.observe (act >>= f) w =
      match Models2Group4.observe act w with
      | none => none
      | some (.error e, w') => some (.error e, w')
      | some (.ok a, w') => Models2Group4.observe (f a) w' := by
  unfold Models2Group4.observe
  simp only [ExceptT.run, StateT.run, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    StateT.bind, Option.bind]
  cases act w with
  | none => rfl
  | some p => rcases p with ⟨r, w'⟩; cases r <;> rfl

private theorem observe_record {E W α Event : Type}
    (ev : Event) (act : Models2Group4.ObservationM E W α) (w : W) (evs : List Event) :
    Models2Group4.observe (Models2Group4.record ev act) (w, evs) =
      match Models2Group4.observe act w with
      | none => none
      | some (res, w') => some (res, (w', evs ++ [ev])) := by
  unfold Models2Group4.record
  simp only [Models2Group4.observe, ExceptT.run, ExceptT.mk, StateT.run, StateT.mk,
    Bind.bind, Option.bind, Pure.pure]
  cases act w <;> rfl

private theorem observe_recordResult {E W α Event : Type}
    (ev : Except (JuliaLean.base.loading.Models2Group4.DispatchError E) α → Event)
    (act : Models2Group4.ObservationM E W α) (w : W) (evs : List Event) :
    Models2Group4.observe (Models2Group4.recordResult ev act) (w, evs) =
      match Models2Group4.observe act w with
      | none => none
      | some (res, w') => some (res, (w', evs ++ [ev res])) := by
  unfold Models2Group4.recordResult
  simp only [Models2Group4.observe, ExceptT.run, ExceptT.mk, StateT.run, StateT.mk,
    Bind.bind, Option.bind, Pure.pure]
  cases act w <;> rfl

private theorem observe_recordPackageStep {E W α Event : Type}
    (ev : W → Except (JuliaLean.base.loading.Models2Group4.DispatchError E) α → W → Event)
    (act : Models2Group4.ObservationM E W α) (w : W) (evs : List Event) :
    Models2Group4.observe (Models2Group4.recordPackageStep ev act) (w, evs) =
      match Models2Group4.observe act w with
      | none => none
      | some (res, w') => some (res, (w', evs ++ [ev w res w'])) := by
  unfold Models2Group4.recordPackageStep
  simp only [Models2Group4.observe, ExceptT.run, ExceptT.mk, StateT.run, StateT.mk,
    Bind.bind, Option.bind, Pure.pure]
  cases act w <;> rfl

private theorem observe_liftCoreAction {W L α : Type}
    (action : JuliaLean.base.boot.CoreM W L α) (world : W) :
    Models2Group4.observe (JuliaLean.base.loading.Models2Group4.liftCoreAction action) world =
      match action world with
      | none => none
      | some (.ok (value, fw)) => some (.ok value, fw)
      | some (.error (error, fw)) => some (.error (.other error), fw) := by
  unfold Models2Group4.observe JuliaLean.base.loading.Models2Group4.liftCoreAction
  simp only [ExceptT.run, ExceptT.mk, StateT.run, StateT.mk, Bind.bind, Option.bind, Pure.pure]
  cases action world with
  | none => rfl
  | some res => cases res <;> rfl

-- 27. models2-g4-core-action-adapter
theorem coreAdapterCorrect_proven :
    Models2Group4.CoreAdapterCorrect := by
  intro W L A action world
  simp only [observe_liftCoreAction]
  cases action world with
  | none =>
      exact And.intro (Iff.intro (fun _ => rfl) (fun _ => rfl))
        (And.intro (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))
  | some res =>
      cases res with
      | ok p =>
          rcases p with ⟨val, fw⟩
          refine And.intro (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
            (And.intro ?_ (fun _ _ h => nomatch h))
          intro v f h
          injection h with h1
          injection h1 with h2
          rcases h2 with ⟨rfl, rfl⟩
          rfl
      | error p =>
          rcases p with ⟨err, fw⟩
          refine And.intro (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
            (And.intro (fun _ _ h => nomatch h) ?_)
          intro e f h
          injection h with h1
          injection h1 with h2
          rcases h2 with ⟨rfl, rfl⟩
          rfl

private theorem observe_tryCatch_ioError {E W Other : Type}
    (act : Models2Group4.ObservationM E W (JuliaLean.base.loading.Models2Group4.DispatchValue Other))
    (world : W) :
    Models2Group4.observe
      (tryCatch act (fun (err : JuliaLean.base.loading.Models2Group4.DispatchError E) =>
        match err with
        | .ioError _ => pure (.bool false)
        | _ => throw err)) world =
      match Models2Group4.observe act world with
      | none => none
      | some (.ok val, fw) => some (.ok val, fw)
      | some (.error (.ioError _), fw) => some (.ok (.bool false), fw)
      | some (.error err, fw) => some (.error err, fw) := by
  unfold Models2Group4.observe
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
    ExceptT.run, ExceptT.mk, StateT.run, Bind.bind, StateT.bind, Option.bind,
    Pure.pure, ExceptT.pure, throw, throwThe, MonadExceptOf.throw]
  cases act world with
  | none => rfl
  | some p =>
      rcases p with ⟨res, fw⟩
      cases res with
      | ok val => rfl
      | error err => cases err <;> rfl

private theorem filterInvariant_tryCatch {E W Other : Type}
    (act : Models2Group4.ObservationM E W (JuliaLean.base.loading.Models2Group4.DispatchValue Other))
    (world : W) :
    Models2Group4.FilterInvariant (Models2Group4.observe act world)
      (Models2Group4.observe
        (tryCatch act (fun (err : JuliaLean.base.loading.Models2Group4.DispatchError E) =>
          match err with
          | .ioError _ => pure (.bool false)
          | _ => throw err)) world) := by
  unfold Models2Group4.FilterInvariant Models2Group4.IsIOError
  rw [observe_tryCatch_ioError]
  cases Models2Group4.observe act world with
  | none =>
      exact And.intro (Iff.intro (fun _ => rfl) (fun _ => rfl))
        (And.intro rfl (And.intro (fun _ _ h => nomatch h)
          (And.intro (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))))
  | some p =>
      rcases p with ⟨res, fw⟩
      cases res with
      | ok val =>
          exact And.intro (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
            (And.intro rfl (And.intro (fun _ _ h => h)
              (And.intro (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))))
      | error err =>
          cases err with
          | ioError payload =>
              refine And.intro (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
                (And.intro rfl (And.intro (fun _ _ h => nomatch h)
                  (And.intro ?_ (fun _ _ h => nomatch h))))
              intro e f h
              injection h with hp
              injection hp with he hf
              subst hf
              injection he with he'
              subst he'
              exact And.intro (fun _ => rfl) (fun hno => False.elim (hno ⟨payload, rfl⟩))
          | argumentError payload =>
              refine And.intro (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
                (And.intro rfl (And.intro (fun _ _ h => nomatch h)
                  (And.intro ?_ ?_)))
              · intro e f h
                injection h with hp
                injection hp with he hf
                subst hf
                injection he with he'
                subst he'
                exact And.intro (fun ⟨_, hio⟩ => nomatch hio) (fun _ => rfl)
              · intro e f h ⟨_, hio⟩
                injection h with hp
                injection hp with he _
                injection he with he'
                subst he'
                nomatch hio
          | typeError =>
              refine And.intro (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
                (And.intro rfl (And.intro (fun _ _ h => nomatch h)
                  (And.intro ?_ ?_)))
              · intro e f h
                injection h with hp
                injection hp with he hf
                subst hf
                injection he with he'
                subst he'
                exact And.intro (fun ⟨_, hio⟩ => nomatch hio) (fun _ => rfl)
              · intro e f h ⟨_, hio⟩
                injection h with hp
                injection hp with he _
                injection he with he'
                subst he'
                nomatch hio
          | other payload =>
              refine And.intro (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
                (And.intro rfl (And.intro (fun _ _ h => nomatch h)
                  (And.intro ?_ ?_)))
              · intro e f h
                injection h with hp
                injection hp with he hf
                subst hf
                injection he with he'
                subst he'
                exact And.intro (fun ⟨_, hio⟩ => nomatch hio) (fun _ => rfl)
              · intro e f h ⟨_, hio⟩
                injection h with hp
                injection hp with he _
                injection he with he'
                subst he'
                nomatch hio

private theorem record_tryCatch_events {E W Event Other : Type}
    (ev : Event)
    (act : Models2Group4.ObservationM E W (JuliaLean.base.loading.Models2Group4.DispatchValue Other))
    (world : W) (result : Except (JuliaLean.base.loading.Models2Group4.DispatchError E)
      (JuliaLean.base.loading.Models2Group4.DispatchValue Other))
    (finalWorld : W) (events : List Event)
    (h : Models2Group4.observe
      (tryCatch (Models2Group4.record ev act)
        (fun (err : JuliaLean.base.loading.Models2Group4.DispatchError E) =>
          match err with
          | .ioError _ => pure (.bool false)
          | _ => throw err)) (world, []) = some (result, (finalWorld, events))) :
    events = [ev] := by
  rw [observe_tryCatch_ioError, observe_record] at h
  rcases hobs : Models2Group4.observe act world with _ | ⟨res, fw⟩ <;> rw [hobs] at h
  · nomatch h
  · cases res with
    | ok val =>
        injection h with h1
        injection h1 with _ h2
        injection h2 with _ hev
        exact hev.symm
    | error err =>
        cases err <;> (
          injection h with h1
          injection h1 with _ h2
          injection h2 with _ hev
          exact hev.symm)

-- 28. models2-g4-isaccessibledir
theorem accessibleDirCorrect_proven :
    Models2Group4.AccessibleDirCorrect := by
  intro E W P Other ops path world
  exact ⟨filterInvariant_tryCatch (ops.isdir path) world,
    fun result finalWorld events h => record_tryCatch_events _ (ops.isdir path) world result finalWorld events h⟩

-- 29. models2-g4-isaccessiblefile
theorem accessibleFileCorrect_proven :
    Models2Group4.AccessibleFileCorrect := by
  intro E W P Other ops path world
  exact ⟨filterInvariant_tryCatch (ops.isfile path) world,
    fun result finalWorld events h => record_tryCatch_events _ (ops.isfile path) world result finalWorld events h⟩

-- 30. models2-g4-isaccessiblepath
theorem accessiblePathCorrect_proven :
    Models2Group4.AccessiblePathCorrect := by
  intro E W P Other ops path world
  exact ⟨filterInvariant_tryCatch (ops.ispath path) world,
    fun result finalWorld events h => record_tryCatch_events _ (ops.ispath path) world result finalWorld events h⟩

-- 31. models2-g4-isfile-casesensitive-unix
theorem unixCaseSensitiveCorrect_proven :
    Models2Group4.UnixCaseSensitiveCorrect := by
  intro E W P Other ops path world
  unfold JuliaLean.base.loading.Models2Group4.isFileCaseSensitiveUnix
    JuliaLean.base.loading.Models2Group4.selectedAccessibleFile
    Models2Group4.traceAccessible Models2Group4.accessibilityEvent
  dsimp only
  cases ops.selection path with
  | base =>
      exact ⟨filterInvariant_tryCatch (ops.predicates.isfile path) world,
        fun result finalWorld events h =>
          record_tryCatch_events _ (ops.predicates.isfile path) world result finalWorld events h⟩
  | custom =>
      refine ⟨rfl, fun result finalWorld events h => ?_⟩
      rw [observe_record] at h
      rcases hobs : Models2Group4.observe (ops.custom path) world with _ | ⟨res, fw⟩ <;> rw [hobs] at h
      · nomatch h
      · injection h with h1
        injection h1 with _ h2
        injection h2 with _ hev
        exact hev.symm

-- 32. models2-g4-parsed-toml-default
theorem parsedTomlDefaultCorrect_proven :
    Models2Group4.ParsedTomlDefaultCorrect := by
  intro E W S Cache Lock Result ops projectFile world
  refine ⟨rfl, fun result finalWorld events h => ?_⟩
  unfold JuliaLean.base.loading.Models2Group4.parsedTomlDefault
    Models2Group4.traceParsedTomlDefault at h
  dsimp only at h
  rw [observe_recordResult] at h
  rcases hobs : Models2Group4.observe (ops.parsedToml projectFile ops.tomlCache ops.requireLock) world with _ | ⟨res, fw⟩ <;>
    rw [hobs] at h
  · nomatch h
  · injection h with h1
    injection h1 with hres h2
    subst hres
    injection h2 with _ hev
    exact hev.symm

-- 33. models2-g4-nothing-or-first
theorem nothingOrFirstCorrect_proven :
    Models2Group4.NothingOrFirstCorrect := by
  intro E W A B ops world
  refine ⟨rfl, fun _ => rfl, fun input result finalWorld events h => ?_⟩
  cases input with
  | none =>
      unfold JuliaLean.base.loading.Models2Group4.nothingOrFirst Models2Group4.observe at h
      simp only [ExceptT.run, StateT.run, Pure.pure, ExceptT.pure] at h
      injection h with h1
      injection h1 with hres h2
      injection h2 with hfw hev
      exact ⟨hev.symm, hres.symm, hfw.symm⟩
  | some value =>
      unfold JuliaLean.base.loading.Models2Group4.nothingOrFirst at h
      dsimp only at h
      rw [observe_recordResult] at h
      rcases hobs : Models2Group4.observe (ops.first value) world with _ | ⟨res, fw⟩ <;> rw [hobs] at h
      · nomatch h
      · injection h with h1
        injection h1 with hres h2
        subst hres
        injection h2 with _ hev
        exact hev.symm

-- 34. models2-g4-cache-flags-six
theorem cacheFlagsSixCorrect_proven :
    Models2Group4.CacheFlagsSixCorrect := by
  intro E W Use Debug Bounds Inline Opt Coverage Result ops
    usePkgimages debugLevel checkBounds inlineValue optLevel coverage world
  dsimp only
  unfold JuliaLean.base.loading.Models2Group4.cacheFlagsSix
    Models2Group4.traceFlagSeven
  dsimp only
  rw [observe_recordPackageStep]
  cases Models2Group4.observe
      (ops.constructSeven usePkgimages debugLevel checkBounds inlineValue optLevel coverage none) world with
  | none =>
      exact And.intro rfl (And.intro (fun _ _ _ h => nomatch h)
        (Iff.intro (fun _ => rfl) (fun _ => rfl)))
  | some p =>
      rcases p with ⟨res, fw⟩
      refine And.intro rfl (And.intro ?_ (Iff.intro (fun h => nomatch h) (fun h => nomatch h)))
      intro result after events h
      injection h with h1
      injection h1 with hres h2
      injection h2 with hafter hev
      subst hres hafter
      exact hev.symm

-- 35. models2-g4-package-get-here
theorem packageGetHereCorrect_proven :
    Models2Group4.PackageGetHereCorrect := by
  intro E W P U Other ops projectFile name world
  unfold JuliaLean.base.loading.Models2Group4.packageGetHere
    Models2Group4.tracePackageHere Models2Group4.PackageHereTrace
    Models2Group4.PackageHereDiverges
  dsimp only
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  cases Models2Group4.observe (ops.explicitProjectDepsGet projectFile name) world with
  | none =>
      exact And.intro (fun _ _ _ h => nomatch h)
        (Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl))
  | some p =>
      rcases p with ⟨res, w1⟩
      cases res with
      | error err =>
          refine And.intro ?_
            (Iff.intro (fun h => nomatch h) (fun h => by rcases h with h | ⟨_, _, h, _⟩ <;> nomatch h))
          intro result finalWorld events h
          injection h with h1
          injection h1 with hres h2
          injection h2 with hfw hev
          subst hres hfw
          exact Or.inl ⟨err, hev.symm, rfl⟩
      | ok opt =>
          cases opt with
          | none =>
              refine And.intro ?_
                (Iff.intro (fun h => nomatch h) (fun h => by rcases h with h | ⟨_, _, h, _⟩ <;> nomatch h))
              intro result finalWorld events h
              injection h with h1
              injection h1 with hres h2
              injection h2 with hfw hev
              subst hres hfw
              exact Or.inr (Or.inl ⟨_, hev.symm, rfl, rfl, rfl⟩)
          | some dep =>
              dsimp only
              rw [observe_recordPackageStep]
              cases h2 : Models2Group4.observe (ops.constructPkgId dep name) w1 with
              | none =>
                  exact And.intro (fun _ _ _ h => nomatch h)
                    (Iff.intro (fun _ => Or.inr ⟨dep, w1, rfl, h2⟩) (fun _ => rfl))
              | some p2 =>
                  rcases p2 with ⟨res2, w2⟩
                  refine And.intro ?_
                    (Iff.intro (fun h => nomatch h) (fun h => by
                      rcases h with h | ⟨d, w', h1, hnone⟩
                      · nomatch h
                      · injection h1 with h1'
                        injection h1' with hd hw
                        injection hd with hd'
                        injection hd' with hd''
                        subst hd'' hw
                        rw [h2] at hnone
                        nomatch hnone))
                  intro result finalWorld events h
                  injection h with h1
                  injection h1 with hres h3
                  injection h3 with hfw hev
                  subst hres hfw
                  exact Or.inr (Or.inr ⟨dep, w1, hev.symm⟩)

-- 36. models2-g4-workspace-manifest
theorem workspaceManifestCorrect_proven :
    Models2Group4.WorkspaceManifestCorrect := by
  intro E W P B R ops projectFile world
  unfold JuliaLean.base.loading.Models2Group4.workspaceManifest
    Models2Group4.traceWorkspace
  dsimp only
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  cases Models2Group4.observe (ops.baseProject projectFile) world with
  | none =>
      exact And.intro (fun _ _ _ h => nomatch h)
        (Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl))
  | some p =>
      rcases p with ⟨res, w1⟩
      cases res with
      | error err =>
          refine And.intro ?_
            (Iff.intro (fun h => nomatch h) (fun h => by rcases h with h | ⟨_, _, h, _⟩ <;> nomatch h))
          intro result finalWorld events h
          injection h with h1
          injection h1 with hres h2
          injection h2 with hfw hev
          subst hres hfw
          exact Or.inl ⟨err, hev.symm, rfl⟩
      | ok opt =>
          cases opt with
          | none =>
              refine And.intro ?_
                (Iff.intro (fun h => nomatch h) (fun h => by rcases h with h | ⟨_, _, h, _⟩ <;> nomatch h))
              intro result finalWorld events h
              injection h with h1
              injection h1 with hres h2
              injection h2 with hfw hev
              subst hres hfw
              exact Or.inr (Or.inl ⟨hev.symm, rfl⟩)
          | some base =>
              dsimp only
              rw [observe_recordPackageStep]
              cases h2 : Models2Group4.observe (ops.projectFileManifestPath base) w1 with
              | none =>
                  exact And.intro (fun _ _ _ h => nomatch h)
                    (Iff.intro (fun _ => Or.inr ⟨base, w1, rfl, h2⟩) (fun _ => rfl))
              | some p2 =>
                  rcases p2 with ⟨res2, w2⟩
                  refine And.intro ?_
                    (Iff.intro (fun h => nomatch h) (fun h => by
                      rcases h with h | ⟨b, w', h1, hnone⟩
                      · nomatch h
                      · injection h1 with h1'
                        injection h1' with hb hw
                        injection hb with hb'
                        injection hb' with hb''
                        subst hb'' hw
                        rw [h2] at hnone
                        nomatch hnone))
                  intro result finalWorld events h
                  injection h with h1
                  injection h1 with hres h3
                  injection h3 with hfw hev
                  subst hres hfw
                  exact Or.inr (Or.inr ⟨base, w1, hev.symm⟩)

-- 37. models2-g4-ocachefile-from-cachefile
theorem objectCachefileCorrect_proven :
    Models2Group4.ObjectCachefileCorrect := by
  intro E W P Chopped R ops input world
  unfold JuliaLean.base.loading.Models2Group4.ocachefileFromCachefile
    Models2Group4.traceObjectCache
    JuliaLean.base.loading.Models2Group4.cacheJiLiteral
    JuliaLean.base.loading.Models2Group4.cacheDotLiteral
  dsimp only
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  cases Models2Group4.observe (ops.chopSuffix input ⟨[46, 106, 105], by decide⟩) world with
  | none =>
      exact And.intro (fun _ _ _ h => nomatch h)
        (Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl))
  | some p =>
      rcases p with ⟨res, w1⟩
      cases res with
      | error err =>
          refine And.intro ?_
            (Iff.intro (fun h => nomatch h) (fun h => by rcases h with h | ⟨_, _, h, _⟩ <;> nomatch h))
          intro result finalWorld events h
          injection h with h1
          injection h1 with hres h2
          injection h2 with hfw hev
          subst hres hfw
          exact Or.inl ⟨⟨[46, 106, 105], by decide⟩, err, rfl, hev.symm, rfl⟩
      | ok chopped =>
          dsimp only
          rw [observe_recordPackageStep]
          cases h2 : Models2Group4.observe (ops.string chopped ⟨[46], by decide⟩ ops.dlExtension) w1 with
          | none =>
              exact And.intro (fun _ _ _ h => nomatch h)
                (Iff.intro (fun _ => Or.inr ⟨chopped, w1, rfl, h2⟩) (fun _ => rfl))
          | some p2 =>
              rcases p2 with ⟨res2, w2⟩
              refine And.intro ?_
                (Iff.intro (fun h => nomatch h) (fun h => by
                  rcases h with h | ⟨c, w', h1, hnone⟩
                  · nomatch h
                  · injection h1 with h1'
                    injection h1' with hc hw
                    injection hc with hc'
                    subst hc' hw
                    rw [h2] at hnone
                    nomatch hnone))
              intro result finalWorld events h
              injection h with h1
              injection h1 with hres h3
              injection h3 with hfw hev
              subst hres hfw
              exact Or.inr ⟨⟨[46, 106, 105], by decide⟩, ⟨[46], by decide⟩,
                chopped, w1, rfl, rfl, hev.symm⟩

private theorem jstr_ext {a b : JuliaLean.Strings.JStr} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; dsimp only at h; subst h; rfl

-- 38. models2-g4-show-precompilable-error
theorem showPrecompilableErrorCorrect_proven :
    Models2Group4.ShowPrecompilableErrorCorrect := by
  intro E W IO R ops io ex world
  unfold JuliaLean.base.loading.Models2Group4.showPrecompilableError
    Models2Group4.tracePrecompilableShow
  dsimp only
  rw [observe_recordPackageStep]
  have hbytes : JuliaLean.base.loading.Models2Group4.precompilableErrorMessage.bytes =
      "Error when precompiling module, potentially caused by a __precompile__(false) declaration in the module.".toUTF8.toList := by
    simp only [String.toUTF8_eq_toByteArray, JuliaLean.base.loading.Models2Group4.hintByteList]
    rfl
  cases h : Models2Group4.observe (ops.print io JuliaLean.base.loading.Models2Group4.precompilableErrorMessage) world with
  | none =>
      exact And.intro (fun _ _ _ h1 => nomatch h1)
        (Iff.intro (fun _ => ⟨JuliaLean.base.loading.Models2Group4.precompilableErrorMessage, hbytes, h⟩)
         (fun _ => rfl))
  | some p =>
      rcases p with ⟨res, fw⟩
      refine And.intro ?_
        (Iff.intro (fun h1 => nomatch h1) (fun ⟨t, ht, hnone⟩ => by
          have heq : t = JuliaLean.base.loading.Models2Group4.precompilableErrorMessage :=
            jstr_ext (ht.trans hbytes.symm)
          subst heq
          rw [h] at hnone
          nomatch hnone))
      intro result finalWorld events h1
      injection h1 with h2
      injection h2 with hres h3
      injection h3 with hfw hev
      subst hres hfw
      exact ⟨JuliaLean.base.loading.Models2Group4.precompilableErrorMessage, hbytes, hev.symm⟩

-- 39. models2-g4-include-string-identity
theorem includeStringIdentityCorrect_proven :
    Models2Group4.IncludeStringIdentityCorrect := by
  refine ⟨rfl, fun E W Mod Custom R ops mod code filename world => ⟨rfl, ?_, ?_⟩⟩
  · intro result finalWorld events h
    unfold JuliaLean.base.loading.Models2Group4.includeStringIdentity
      Models2Group4.traceIncludeIdentity at h
    dsimp only at h
    rw [observe_recordResult] at h
    rcases hobs : Models2Group4.observe (ops.includeString .identity mod code filename) world with _ | ⟨res, fw⟩ <;>
      rw [hobs] at h
    · nomatch h
    · injection h with h1
      injection h1 with hres h2
      subst hres
      injection h2 with _ hev
      exact hev.symm
  · dsimp only [JuliaLean.base.loading.Models2Group4.includeStringIdentityDefault,
      JuliaLean.base.loading.Models2Group4.selectedIncludeStringIdentity,
      JuliaLean.base.loading.Models2Group4.includeDefaultFilename,
      Models2Group4.traceIncludeIdentity]
    cases ops.explicitSelection mod code (.native ⟨[115, 116, 114, 105, 110, 103], by decide⟩) with
    | base =>
        refine ⟨rfl, fun result finalWorld events h => ?_⟩
        unfold JuliaLean.base.loading.Models2Group4.includeStringIdentity at h
        dsimp only at h
        rw [observe_recordResult] at h
        rcases hobs : Models2Group4.observe
            (ops.includeString .identity mod code (.native ⟨[115, 116, 114, 105, 110, 103], by decide⟩)) world with _ | ⟨res, fw⟩ <;>
          rw [hobs] at h
        · nomatch h
        · injection h with h1
          injection h1 with hres h2
          subst hres
          injection h2 with _ hev
          exact hev.symm
    | custom =>
        refine ⟨rfl, fun result finalWorld events h => ?_⟩
        dsimp only at h
        rw [observe_recordResult] at h
        rcases hobs : Models2Group4.observe
            (ops.customExplicit mod code (.native ⟨[115, 116, 114, 105, 110, 103], by decide⟩)) world with _ | ⟨res, fw⟩ <;>
          rw [hobs] at h
        · nomatch h
        · injection h with h1
          injection h1 with hres h2
          subst hres
          injection h2 with _ hev
          exact hev.symm

-- 40. models2-g4-preferences-blob-stream
theorem preferenceBlobStreamCorrect_proven :
    Models2Group4.PreferenceBlobStreamCorrect := by
  intro E W IO Path Header R ops io path world
  unfold JuliaLean.base.loading.Models2Group4.preferencesBlobStream
    Models2Group4.tracePreferenceBlobStream
  dsimp only
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  cases Models2Group4.observe (ops.parseHeader io path) world with
  | none =>
      exact And.intro (fun _ _ _ h => nomatch h)
        (Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl))
  | some p =>
      rcases p with ⟨res, w1⟩
      cases res with
      | error err =>
          refine And.intro ?_
            (Iff.intro (fun h => nomatch h) (fun h => by rcases h with h | ⟨_, _, h, _⟩ <;> nomatch h))
          intro result finalWorld events h
          injection h with h1
          injection h1 with hres h2
          injection h2 with hfw hev
          subst hres hfw
          exact Or.inl ⟨err, hev.symm, rfl⟩
      | ok header =>
          dsimp only
          rw [observe_recordPackageStep]
          cases h2 : Models2Group4.observe (ops.getindex header (JInt.lit .i64 5)) w1 with
          | none =>
              exact And.intro (fun _ _ _ h => nomatch h)
                (Iff.intro (fun _ => Or.inr ⟨header, w1, rfl, h2⟩) (fun _ => rfl))
          | some p2 =>
              rcases p2 with ⟨res2, w2⟩
              refine And.intro ?_
                (Iff.intro (fun h => nomatch h) (fun h => by
                  rcases h with h | ⟨hdr, w', h1, hnone⟩
                  · nomatch h
                  · injection h1 with h1'
                    injection h1' with hhdr hw
                    injection hhdr with hhdr'
                    subst hhdr' hw
                    rw [h2] at hnone
                    nomatch hnone))
              intro result finalWorld events h
              injection h with h1
              injection h1 with hres h3
              injection h3 with hfw hev
              subst hres hfw
              exact Or.inr ⟨header, w1, JInt.lit .i64 5, lit_i64_five_val, hev.symm⟩

-- 41. models2-g4-toml-egal-identity
theorem tomlEgalIdentityCorrect_proven :
    Models2Group4.TomlEgalIdentityCorrect := by
  intro W L core left right
  exact ⟨rfl, rfl, fun _ h => h⟩

-- 42. models2-g4-include-dependency-internal
private theorem observe_recordSortCoreStep {W L α Event : Type}
    (ev : W → Except (JuliaLean.base.loading.Models2Group4.GenericValue L) α → W → Event)
    (act : JuliaLean.base.boot.CoreM W L α) (w : W) (evs : List Event) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.liftCoreAction
        (Models2Group4.recordSortCoreStep ev act)) (w, evs) =
      match act w with
      | none => none
      | some (.ok (val, fw)) => some (.ok val, (fw, evs ++ [ev w (.ok val) fw]))
      | some (.error (err, fw)) => some (.error (.other err), (fw, evs ++ [ev w (.error err) fw])) := by
  unfold Models2Group4.observe JuliaLean.base.loading.Models2Group4.liftCoreAction
    Models2Group4.recordSortCoreStep
  simp only [ExceptT.run, ExceptT.mk, StateT.run, StateT.mk, Bind.bind, Option.bind, Pure.pure]
  cases act w with
  | none => rfl
  | some res => cases res <;> rfl

theorem includeDependencyInternalCorrect_proven :
    Models2Group4.IncludeDependencyInternalCorrect := by
  intro W L Mod Path ops otherCore module path content directory world
  have haux : ∀ (c d : Bool),
      (∀ result finalWorld events,
        Models2Group4.observe
          (JuliaLean.base.loading.Models2Group4.includeDependencyInternal
            (Models2Group4.traceDependencyWrapper ops otherCore) module path c d) (world, []) =
          some (result, (finalWorld, events)) →
        Models2Group4.DependencyWrapperTrace ops.trackDependenciesRef ops.requireDependencies
          module path c d world result finalWorld events) ∧
      (Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.includeDependencyInternal ops module path c d) world = none ↔
        Models2Group4.DependencyWrapperDiverges ops module path c d world) := by
    intro c d
    unfold JuliaLean.base.loading.Models2Group4.includeDependencyInternal
      Models2Group4.traceDependencyWrapper Models2Group4.DependencyWrapperTrace
      Models2Group4.DependencyWrapperDiverges
    dsimp only
    rw [observe_bind, observe_bind, observe_recordSortCoreStep, observe_liftCoreAction]
    cases ops.core.getfield ops.trackDependenciesRef (.symbol "x") world with
    | none =>
        exact And.intro (fun _ _ _ h => nomatch h)
          (Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl))
    | some res =>
        cases res with
        | error p =>
            rcases p with ⟨err, fw⟩
            refine And.intro ?_
              (Iff.intro (fun h => nomatch h) (fun h => by rcases h with h | ⟨_, _, h, _⟩ <;> nomatch h))
            intro result finalWorld events h
            injection h with h1
            injection h1 with hres h2
            injection h2 with hfw hev
            subst hres hfw
            exact Or.inl ⟨err, hev.symm, rfl⟩
        | ok p =>
            rcases p with ⟨tracking, w1⟩
            dsimp only
            rw [observe_recordPackageStep]
            cases h2 : Models2Group4.observe
                (ops.selectedRecord ops.requireDependencies tracking module path c d) w1 with
            | none =>
                exact And.intro (fun _ _ _ h => nomatch h)
                  (Iff.intro (fun _ => Or.inr ⟨tracking, w1, rfl, h2⟩) (fun _ => rfl))
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                refine And.intro ?_
                  (Iff.intro (fun h => nomatch h) (fun h => by
                    rcases h with h | ⟨t, w', h1, hnone⟩
                    · nomatch h
                    · injection h1 with h1'
                      injection h1' with ht'
                      rcases ht' with ⟨rfl, rfl⟩
                      rw [h2] at hnone
                      nomatch hnone))
                intro result finalWorld events h
                injection h with h1
                injection h1 with hres h3
                injection h3 with hfw hev
                subst hres hfw
                exact Or.inr ⟨tracking, w1, hev.symm⟩
  exact ⟨(haux content directory).1, (haux content directory).2, (haux true false).1⟩

-- 43. models2-g4-include-dependency-public
theorem includeDependencyPublicCorrect_proven :
    Models2Group4.IncludeDependencyPublicCorrect := by
  intro W L Mod Path ops otherCore path content world
  have haux : ∀ (c : Bool),
      (∀ result finalWorld events,
        Models2Group4.observe
          (JuliaLean.base.loading.Models2Group4.includeDependencyPublic
            (Models2Group4.traceDependencyPublic ops otherCore) path c) (world, []) =
          some (result, (finalWorld, events)) →
        Models2Group4.DependencyPublicTrace ops path c world result finalWorld events) ∧
      (Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.includeDependencyPublic ops path c) world = none ↔
        Models2Group4.DependencyPublicDiverges ops path c world) := by
    intro c
    unfold JuliaLean.base.loading.Models2Group4.includeDependencyPublic
      JuliaLean.base.loading.Models2Group4.selectedDependencyInternal
      Models2Group4.traceDependencyPublic Models2Group4.DependencyPublicTrace
      Models2Group4.DependencyPublicDiverges
    dsimp only
    cases ops.selection ops.mainModule path with
    | custom =>
        simp only [observe_bind, observe_recordPackageStep]
        cases h : Models2Group4.observe (ops.customInternal ops.mainModule path c true) world with
        | none =>
            exact And.intro (fun _ _ _ h1 => nomatch h1)
              (Iff.intro (fun _ => rfl) (fun _ => rfl))
        | some p =>
            rcases p with ⟨res, fw⟩
            cases res with
            | error err =>
                refine And.intro ?_ (Iff.intro (fun h1 => nomatch h1) (fun h1 => nomatch h1))
                intro result finalWorld events h1
                injection h1 with h2
                injection h2 with hres h3
                injection h3 with hfw hev
                subst hres hfw
                exact ⟨.error err, hev.symm, rfl⟩
            | ok val =>
                dsimp only
                refine And.intro ?_ (Iff.intro (fun h1 => nomatch h1) (fun h1 => nomatch h1))
                intro result finalWorld events h1
                injection h1 with h2
                injection h2 with hres h3
                injection h3 with hfw hev
                subst hres hfw
                exact ⟨.ok val, hev.symm, rfl⟩
    | base =>
        simp only [observe_bind]
        unfold JuliaLean.base.loading.Models2Group4.includeDependencyInternal
          Models2Group4.traceDependencyWrapper Models2Group4.DependencyWrapperTrace
          Models2Group4.DependencyWrapperDiverges
        dsimp only
        rw [observe_bind, observe_bind, observe_recordSortCoreStep, observe_liftCoreAction]
        cases ops.internalOps.core.getfield ops.internalOps.trackDependenciesRef (.symbol "x") world with
        | none =>
            exact And.intro (fun _ _ _ h1 => nomatch h1)
              (Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl))
        | some res =>
            cases res with
            | error p =>
                rcases p with ⟨err, fw⟩
                refine And.intro ?_
                  (Iff.intro (fun h1 => nomatch h1) (fun h1 => by rcases h1 with h1 | ⟨_, _, h1, _⟩ <;> nomatch h1))
                intro result finalWorld events h1
                injection h1 with h2
                injection h2 with hres h3
                injection h3 with hfw hev
                subst hres hfw
                exact ⟨.error (.other err), Or.inl ⟨err, hev.symm, rfl⟩, rfl⟩
            | ok p =>
                rcases p with ⟨tracking, w1⟩
                dsimp only
                rw [observe_recordPackageStep]
                cases h2 : Models2Group4.observe
                    (ops.internalOps.selectedRecord ops.internalOps.requireDependencies tracking
                      ops.mainModule path c true) w1 with
                | none =>
                    exact And.intro (fun _ _ _ h1 => nomatch h1)
                      (Iff.intro (fun _ => Or.inr ⟨tracking, w1, rfl, h2⟩) (fun _ => rfl))
                | some p2 =>
                    rcases p2 with ⟨res2, w2⟩
                    cases res2 with
                    | error err2 =>
                        refine And.intro ?_
                          (Iff.intro (fun h1 => nomatch h1) (fun h1 => by
                            rcases h1 with h1 | ⟨t, w', h1, hnone⟩
                            · nomatch h1
                            · injection h1 with h1'
                              injection h1' with ht'
                              rcases ht' with ⟨rfl, rfl⟩
                              rw [h2] at hnone
                              nomatch hnone))
                        intro result finalWorld events h1
                        injection h1 with h3
                        injection h3 with hres h4
                        injection h4 with hfw hev
                        subst hres hfw
                        exact ⟨.error err2, Or.inr ⟨tracking, w1, hev.symm⟩, rfl⟩
                    | ok val2 =>
                        dsimp only
                        refine And.intro ?_
                          (Iff.intro (fun h1 => nomatch h1) (fun h1 => by
                            rcases h1 with h1 | ⟨t, w', h1, hnone⟩
                            · nomatch h1
                            · injection h1 with h1'
                              injection h1' with ht'
                              rcases ht' with ⟨rfl, rfl⟩
                              rw [h2] at hnone
                              nomatch hnone))
                        intro result finalWorld events h1
                        injection h1 with h3
                        injection h3 with hres h4
                        injection h4 with hfw hev
                        subst hres hfw
                        exact ⟨.ok val2, Or.inr ⟨tracking, w1, hev.symm⟩, rfl⟩
  exact ⟨(haux content).1, (haux content).2, (haux true).1⟩

-- 44. models2-g4-filter-preferences
private theorem observe_liftCoreAction_typeassert {W L : Type}
    (core : JuliaLean.base.boot.CoreOps W L)
    (val ty : JuliaLean.base.loading.Models2Group4.GenericValue L) (w : W) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.liftCoreAction
        (JuliaLean.base.boot.typeassert core val ty)) w =
      if core.isa val ty then some (.ok val, w)
      else some (.error (.other (.leaf (core.obj
        (.typeError (.symbol "typeassert") (.leaf (core.str "")) ty val)))), w) := by
  unfold JuliaLean.base.boot.typeassert JuliaLean.base.boot.throwTypeError
    JuliaLean.base.boot.throwObj JuliaLean.base.boot.objV JuliaLean.base.boot.strV
  cases core.isa val ty <;> rfl

theorem filterPreferencesCorrect_proven :
    Models2Group4.FilterPreferencesCorrect := by
  intro W L ops otherCore prefs pkgName world
  unfold JuliaLean.base.loading.Models2Group4.filterPreferences
    Models2Group4.traceFilterPreferences JuliaLean.base.boot.nothingV
  dsimp only
  cases hsame : ops.core.same pkgName (.leaf ops.core.nothing) with
  | true =>
      refine And.intro ?_ (Iff.intro (fun h => nomatch h) (fun ⟨h, _⟩ => nomatch h))
      intro result finalWorld events h
      unfold Models2Group4.observe at h
      simp only [ExceptT.run, StateT.run, Pure.pure, ExceptT.pure] at h
      injection h with h1
      injection h1 with hres h2
      injection h2 with hfw hev
      exact Or.inl ⟨rfl, hres.symm, hfw.symm, hev.symm⟩
  | false =>
      have hne : ¬ (false = true) := by decide
      rw [ite_eq_right hne, ite_eq_right hne, observe_bind, observe_bind, observe_recordPackageStep]
      cases hget : Models2Group4.observe (ops.getDefaultFactory ops.dictType prefs pkgName) world with
      | none =>
          exact And.intro (fun _ _ _ h => nomatch h)
            (Iff.intro (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl))
      | some p =>
          rcases p with ⟨res, w1⟩
          cases res with
          | error err =>
              refine And.intro ?_ (Iff.intro (fun h => nomatch h) (fun ⟨_, h⟩ => nomatch h))
              intro result finalWorld events h
              injection h with h1
              injection h1 with hres h2
              injection h2 with hfw hev
              subst hres hfw
              exact Or.inr ⟨rfl, .error err, hev.symm, rfl⟩
          | ok val =>
              dsimp only
              rw [observe_liftCoreAction_typeassert, observe_liftCoreAction_typeassert]
              cases hisa : ops.core.isa val ops.dictType with
              | true =>
                  dsimp only [↓reduceIte]
                  refine And.intro ?_ (Iff.intro (fun h => nomatch h) (fun ⟨_, h⟩ => nomatch h))
                  intro result finalWorld events h
                  injection h with h1
                  injection h1 with hres h2
                  injection h2 with hfw hev
                  subst hres hfw
                  exact Or.inr ⟨rfl, .ok val, hev.symm, Or.inl ⟨hisa, rfl⟩⟩
              | false =>
                  dsimp only [Bool.false_eq_true, ↓reduceIte]
                  refine And.intro ?_ (Iff.intro (fun h => nomatch h) (fun ⟨_, h⟩ => nomatch h))
                  intro result finalWorld events h
                  injection h with h1
                  injection h1 with hres h2
                  injection h2 with hfw hev
                  subst hres hfw
                  exact Or.inr ⟨rfl, .ok val, hev.symm, Or.inr ⟨hisa, rfl⟩⟩

-- 45. models2-g4-package-loaded-error
theorem packageLoadedErrorCorrect_proven :
    Models2Group4.PackageLoadedErrorCorrect := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun E W P Name Text R ops pkg world => ?_⟩
  unfold JuliaLean.base.loading.Models2Group4.checkPackageModuleLoadedError
    Models2Group4.tracePackageLoadedError
  dsimp only
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  cases h1 : Models2Group4.observe (ops.getName pkg) world with
  | none =>
      exact And.intro (fun _ _ _ h => nomatch h)
        (Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl))
  | some p1 =>
      rcases p1 with ⟨res1, w1⟩
      cases res1 with
      | error err1 =>
          refine And.intro ?_
            (Iff.intro (fun h => nomatch h) (fun h => by
              rcases h with h | ⟨_, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ <;> nomatch h))
          intro result finalWorld events h
          injection h with ha
          injection ha with hres hb
          injection hb with hfw hev
          subst hres hfw
          exact Or.inl ⟨err1, hev.symm, rfl⟩
      | ok n1 =>
          dsimp only
          rw [observe_bind, observe_bind, observe_recordPackageStep]
          cases h2 : Models2Group4.observe (ops.getName pkg) w1 with
          | none =>
              exact And.intro (fun _ _ _ h => nomatch h)
                (Iff.intro (fun _ => Or.inr (Or.inl ⟨n1, w1, rfl, h2⟩)) (fun _ => rfl))
          | some p2 =>
              rcases p2 with ⟨res2, w2⟩
              cases res2 with
              | error err2 =>
                  refine And.intro ?_
                    (Iff.intro (fun h => nomatch h) (fun h => by
                      rcases h with h | ⟨fn, w1', ha, hb⟩ | ⟨fn, sn, w1', w2', ha, hb, _⟩ |
                        ⟨fn, sn, _, w1', w2', _, ha, hb, _⟩
                      · nomatch h
                      · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                        subst hfn' hw1; rw [h2] at hb; nomatch hb
                      · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                        subst hfn' hw1; rw [h2] at hb; nomatch hb
                      · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                        subst hfn' hw1; rw [h2] at hb; nomatch hb))
                  intro result finalWorld events h
                  injection h with ha
                  injection ha with hres hb
                  injection hb with hfw hev
                  subst hres hfw
                  exact Or.inr (Or.inl ⟨n1, w1, err2, hev.symm, rfl⟩)
              | ok n2 =>
                  dsimp only
                  rw [observe_bind, observe_bind, observe_recordPackageStep]
                  cases h3 : Models2Group4.observe
                      (ops.string JuliaLean.base.loading.Models2Group4.loadedErrorPrefix n1
                        JuliaLean.base.loading.Models2Group4.loadedErrorMiddle n2
                        JuliaLean.base.loading.Models2Group4.loadedErrorSuffix) w2 with
                  | none =>
                      exact And.intro (fun _ _ _ h => nomatch h)
                        (Iff.intro (fun _ => Or.inr (Or.inr (Or.inl ⟨n1, n2, w1, w2, rfl, h2, h3⟩)))
                          (fun _ => rfl))
                  | some p3 =>
                      rcases p3 with ⟨res3, w3⟩
                      cases res3 with
                      | error err3 =>
                          refine And.intro ?_
                            (Iff.intro (fun h => nomatch h) (fun h => by
                              rcases h with h | ⟨fn, w1', ha, hb⟩ | ⟨fn, sn, w1', w2', ha, hb, hc⟩ |
                                ⟨fn, sn, _, w1', w2', _, ha, hb, hc, _⟩
                              · nomatch h
                              · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                                subst hfn' hw1; rw [h2] at hb; nomatch hb
                              · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                                subst hfn' hw1; rw [h2] at hb
                                injection hb with hb'; injection hb' with hsn hw2; injection hsn with hsn'
                                subst hsn' hw2; rw [h3] at hc; nomatch hc
                              · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                                subst hfn' hw1; rw [h2] at hb
                                injection hb with hb'; injection hb' with hsn hw2; injection hsn with hsn'
                                subst hsn' hw2; rw [h3] at hc; nomatch hc))
                          intro result finalWorld events h
                          injection h with ha
                          injection ha with hres hb
                          injection hb with hfw hev
                          subst hres hfw
                          exact Or.inr (Or.inr (Or.inl ⟨n1, n2, w1, w2, _, _, _, err3,
                            ⟨rfl, rfl, rfl⟩, hev.symm, rfl⟩))
                      | ok msg =>
                          dsimp only
                          rw [observe_recordPackageStep]
                          cases h4 : Models2Group4.observe (ops.error msg) w3 with
                          | none =>
                              exact And.intro (fun _ _ _ h => nomatch h)
                                (Iff.intro (fun _ => Or.inr (Or.inr (Or.inr
                                  ⟨n1, n2, msg, w1, w2, w3, rfl, h2, h3, h4⟩))) (fun _ => rfl))
                          | some p4 =>
                              rcases p4 with ⟨res4, w4⟩
                              refine And.intro ?_
                                (Iff.intro (fun h => nomatch h) (fun h => by
                                  rcases h with h | ⟨fn, w1', ha, hb⟩ | ⟨fn, sn, w1', w2', ha, hb, hc⟩ |
                                    ⟨fn, sn, m, w1', w2', w3', ha, hb, hc, hd⟩
                                  · nomatch h
                                  · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                                    subst hfn' hw1; rw [h2] at hb; nomatch hb
                                  · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                                    subst hfn' hw1; rw [h2] at hb
                                    injection hb with hb'; injection hb' with hsn hw2; injection hsn with hsn'
                                    subst hsn' hw2; rw [h3] at hc; nomatch hc
                                  · injection ha with ha'; injection ha' with hfn hw1; injection hfn with hfn'
                                    subst hfn' hw1; rw [h2] at hb
                                    injection hb with hb'; injection hb' with hsn hw2; injection hsn with hsn'
                                    subst hsn' hw2; rw [h3] at hc
                                    injection hc with hc'; injection hc' with hm hw3; injection hm with hm'
                                    subst hm' hw3; rw [h4] at hd; nomatch hd))
                              intro result finalWorld events h
                              injection h with ha
                              injection ha with hres hb
                              injection hb with hfw hev
                              subst hres hfw
                              exact Or.inr (Or.inr (Or.inr ⟨n1, n2, msg, w1, w2, w3, _, _, _,
                                ⟨rfl, rfl, rfl⟩, hev.symm⟩))


private theorem observe_pure {E W α : Type} (a : α) (w : W) :
    Models2Group4.observe (pure a : Models2Group4.ObservationM E W α) w = some (.ok a, w) := rfl

private theorem observe_throw {E W α : Type} (e : JuliaLean.base.loading.Models2Group4.DispatchError E) (w : W) :
    Models2Group4.observe (throw e : Models2Group4.ObservationM E W α) w = some (.error e, w) := rfl

private theorem observe_tryCatch {E W α : Type}
    (body : Models2Group4.ObservationM E W α)
    (handler : JuliaLean.base.loading.Models2Group4.DispatchError E → Models2Group4.ObservationM E W α)
    (w : W) :
    Models2Group4.observe (tryCatch body handler) w =
      match Models2Group4.observe body w with
      | none => none
      | some (.ok a, w1) => some (.ok a, w1)
      | some (.error err, w1) => Models2Group4.observe (handler err) w1 := by
  unfold Models2Group4.observe
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk,
    ExceptT.run, StateT.run, Bind.bind, StateT.bind, Option.bind, Pure.pure]
  cases body w with
  | none => rfl
  | some p1 => rcases p1 with ⟨res, w1⟩; cases res <;> rfl


private theorem observe_recordHintCore {W L α Event : Type}
    (ev : W → Except (JuliaLean.base.loading.Models2Group4.DispatchError (JuliaLean.base.loading.Models2Group4.GenericValue L)) α → W → Event)
    (action : JuliaLean.base.boot.CoreM W L α) (w : W) (evs : List Event) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.liftCoreAction
        (Models2Group4.recordHintCore ev action)) (w, evs) =
      match Models2Group4.observe (JuliaLean.base.loading.Models2Group4.liftCoreAction action) w with
      | none => none
      | some (res, fw) => some (res, (fw, evs ++ [ev w res fw])) := by
  rw [observe_liftCoreAction, observe_liftCoreAction]
  unfold Models2Group4.recordHintCore
  simp only [Bind.bind, Option.bind, Pure.pure]
  cases action w with
  | none => rfl
  | some res => cases res <;> rfl

private theorem observe_selectedAccessibleFile_trace {E W P Other Long Left Right : Type}
    (ops : JuliaLean.base.loading.Models2Group4.AccessibleFileOps (Models2Group4.ObservationM E W) P Other)
    (path : P) (w : W) (evs : List (Models2Group4.CallEvent P Long Left Right)) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.selectedAccessibleFile (E := E)
        (Models2Group4.traceAccessible ops) path) (w, evs) =
      match Models2Group4.observe
          (JuliaLean.base.loading.Models2Group4.selectedAccessibleFile (E := E) ops path) w with
      | none => none
      | some (res, w') =>
          some (res, (w', evs ++ [Models2Group4.accessibilityEvent (ops.selection path) path])) := by
  cases hsel : ops.selection path with
  | custom =>
      simp only [JuliaLean.base.loading.Models2Group4.selectedAccessibleFile,
        Models2Group4.traceAccessible, Models2Group4.accessibilityEvent, hsel]
      rw [observe_record]; cases Models2Group4.observe (ops.custom path) w <;> rfl
  | base =>
      simp only [JuliaLean.base.loading.Models2Group4.selectedAccessibleFile,
        Models2Group4.traceAccessible, Models2Group4.tracePredicates,
        Models2Group4.accessibilityEvent, hsel]
      unfold JuliaLean.base.loading.Models2Group4.isAccessibleFile
      rw [observe_tryCatch, observe_tryCatch, observe_record]
      cases Models2Group4.observe (ops.predicates.isfile path) w with
      | none => rfl
      | some p =>
          rcases p with ⟨res, w'⟩
          cases res with
          | ok v => rfl
          | error err => cases err <;> rfl

-- 2. loading-isfile-casesensitive-windows
theorem windowsCaseSensitiveCorrect_proven :
    Models2Group4.WindowsCaseSensitiveCorrect := by
  intro E W P Other Long Left Right ops path world
  unfold JuliaLean.base.loading.Models2Group4.isFileCaseSensitiveWindows
  dsimp only [Models2Group4.traceWindows]
  rw [observe_bind, observe_selectedAccessibleFile_trace]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro result finalWorld events h
    cases hacc : Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.selectedAccessibleFile (E := E) ops.accessible path) world with
    | none => rw [hacc] at h; nomatch h
    | some p =>
        rcases p with ⟨res, w1⟩
        rw [hacc] at h
        cases res with
        | error err =>
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            exact Or.inl hev.symm
        | ok val =>
            cases val with
            | other v =>
                injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                exact Or.inl hev.symm
            | bool b =>
                cases b with
                | false =>
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    exact Or.inl hev.symm
                | true =>
                    dsimp only at h
                    rw [observe_bind, observe_record] at h
                    cases hlong : Models2Group4.observe (ops.longpath path) w1 with
                    | none => rw [hlong] at h; nomatch h
                    | some p2 =>
                        rcases p2 with ⟨res2, w2⟩
                        rw [hlong] at h
                        cases res2 with
                        | error err =>
                            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                            exact Or.inr (Or.inl hev.symm)
                        | ok long =>
                            dsimp only at h
                            rw [observe_bind, observe_record] at h
                            cases hleft : Models2Group4.observe (ops.basenameLong long) w2 with
                            | none => rw [hleft] at h; nomatch h
                            | some p3 =>
                                rcases p3 with ⟨res3, w3⟩
                                rw [hleft] at h
                                cases res3 with
                                | error err =>
                                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                    exact Or.inr (Or.inr (Or.inl ⟨long, hev.symm⟩))
                                | ok left =>
                                    dsimp only at h
                                    rw [observe_bind, observe_record] at h
                                    cases hright : Models2Group4.observe (ops.basenamePath path) w3 with
                                    | none => rw [hright] at h; nomatch h
                                    | some p4 =>
                                        rcases p4 with ⟨res4, w4⟩
                                        rw [hright] at h
                                        cases res4 with
                                        | error err =>
                                            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨long, hev.symm⟩)))
                                        | ok right =>
                                            dsimp only at h
                                            rw [observe_record] at h
                                            cases heq : Models2Group4.observe (ops.equal left right) w4 with
                                            | none => rw [heq] at h; nomatch h
                                            | some p5 =>
                                                rcases p5 with ⟨res5, w5⟩
                                                rw [heq] at h
                                                injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                                exact Or.inr (Or.inr (Or.inr (Or.inr ⟨long, left, right, hev.symm⟩)))
  · intro finalWorld h; rw [h]; rfl
  · intro value finalWorld h; rw [h]; rfl
  · intro error finalWorld h; rw [h]; rfl
  · intro h; rw [h]

-- 3. loading-sha-abstractstring
private def DigestRunInvariant {E W S Decoded Other : Type}
    (ops : JuliaLean.base.loading.Models2Group4.DigestStringOps (Models2Group4.ObservationM E W) S Decoded Other)
    (kind : JuliaLean.base.loading.Models2Group4.DigestKind)
    (string : S)
    (state : W × List (Models2Group4.DigestEvent E S Decoded Other))
    (out : Except (JuliaLean.base.loading.Models2Group4.DispatchError E)
      (JuliaLean.base.loading.Models2Group4.DigestValue Other) ×
      (W × List (Models2Group4.DigestEvent E S Decoded Other))) : Prop :=
  ∃ events,
    out.2.2 = state.2 ++ events ∧
    Models2Group4.DigestConstructionTrace ops.decodedStringSelection kind string events out.1

private theorem digestFromAbstractStringRun_trace {E W S Decoded Other : Type}
    (ops : JuliaLean.base.loading.Models2Group4.DigestStringOps (Models2Group4.ObservationM E W) S Decoded Other)
    (kind : JuliaLean.base.loading.Models2Group4.DigestKind) :
    ∀ (string : S) (state : W × List (Models2Group4.DigestEvent E S Decoded Other))
      (out : Except (JuliaLean.base.loading.Models2Group4.DispatchError E)
        (JuliaLean.base.loading.Models2Group4.DigestValue Other) ×
        (W × List (Models2Group4.DigestEvent E S Decoded Other))),
      JuliaLean.base.loading.Models2Group4.digestFromAbstractStringRun
        (Models2Group4.traceDigestString ops) kind string state = some out →
      DigestRunInvariant ops kind string state out := by
  refine JuliaLean.base.loading.Models2Group4.digestFromAbstractStringRun.fixpoint_induct
    (Models2Group4.traceDigestString ops) kind
    (fun f => ∀ string state out, f string state = some out →
      DigestRunInvariant ops kind string state out) ?_ ?_
  · exact Lean.Order.admissible_pi_apply
      (P := fun (string : S)
        (g : (W × List (Models2Group4.DigestEvent E S Decoded Other)) →
          Option (Except (JuliaLean.base.loading.Models2Group4.DispatchError E)
            (JuliaLean.base.loading.Models2Group4.DigestValue Other) ×
            (W × List (Models2Group4.DigestEvent E S Decoded Other)))) =>
        ∀ state out, g state = some out → DigestRunInvariant ops kind string state out)
      (fun string => Lean.Order.admissible_pi_apply
        (P := fun (state : W × List (Models2Group4.DigestEvent E S Decoded Other))
          (o : Option (Except (JuliaLean.base.loading.Models2Group4.DispatchError E)
            (JuliaLean.base.loading.Models2Group4.DigestValue Other) ×
            (W × List (Models2Group4.DigestEvent E S Decoded Other)))) =>
          ∀ out, o = some out → DigestRunInvariant ops kind string state out)
        (fun state => Lean.Order.admissible_pi
          (P := fun o out => o = some out → DigestRunInvariant ops kind string state out)
          (fun out => Lean.Order.Option.admissible_eq_some _ out)))
  · intro f ih string state out h
    rcases state with ⟨w, evs⟩
    rcases out with ⟨result, finalWorld, finalEvents⟩
    change (do
      let (decoded, nextWorld) ← Models2Group4.observe ((Models2Group4.traceDigestString ops).hex2bytes string) (w, evs)
      match decoded with
      | .error error => pure (.error error, nextWorld)
      | .ok (.string nextString) =>
          match (Models2Group4.traceDigestString ops).decodedStringSelection kind nextString with
          | .base => f nextString nextWorld
          | .custom => Models2Group4.observe ((Models2Group4.traceDigestString ops).constructString kind nextString) nextWorld
      | .ok (.other value) =>
          Models2Group4.observe ((Models2Group4.traceDigestString ops).constructDecoded kind value) nextWorld) =
      some (result, (finalWorld, finalEvents)) at h
    dsimp only [Models2Group4.traceDigestString] at h
    rw [observe_recordResult] at h
    cases hhex : Models2Group4.observe (ops.hex2bytes string) w with
    | none => rw [hhex] at h; nomatch h
    | some p =>
        rcases p with ⟨decoded, w1⟩
        rw [hhex] at h
        cases decoded with
        | error err =>
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            subst hres
            exact ⟨[.decode string (.error err)], hev.symm, .decoderError string err⟩
        | ok dec =>
            cases dec with
            | other val =>
                dsimp only [Bind.bind, Option.bind] at h
                rw [observe_recordResult] at h
                cases hcon : Models2Group4.observe (ops.constructDecoded kind val) w1 with
                | none => rw [hcon] at h; nomatch h
                | some p2 =>
                    rcases p2 with ⟨res2, w2⟩
                    rw [hcon] at h
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    subst hres
                    refine ⟨[.decode string (.ok (.other val)), .construct kind val res2], ?_,
                      .finished string val res2⟩
                    rw [← hev]; simp only [List.append_assoc]; rfl
            | string nextString =>
                dsimp only [Bind.bind, Option.bind] at h
                cases hsel : ops.decodedStringSelection kind nextString with
                | custom =>
                    rw [hsel, observe_recordResult] at h
                    cases hcon : Models2Group4.observe (ops.constructString kind nextString) w1 with
                    | none => rw [hcon] at h; nomatch h
                    | some p2 =>
                        rcases p2 with ⟨res2, w2⟩
                        rw [hcon] at h
                        injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                        subst hres
                        refine ⟨[.decode string (.ok (.string nextString)),
                          .customConstructor kind nextString res2], ?_,
                          .customString string nextString res2 hsel⟩
                        rw [← hev]; simp only [List.append_assoc]; rfl
                | base =>
                    rw [hsel] at h
                    obtain ⟨tailEvents, htailEv, htailTrace⟩ := ih nextString _ _ h
                    dsimp only at htailEv htailTrace
                    refine ⟨.decode string (.ok (.string nextString)) :: tailEvents, ?_,
                      .recursive string nextString tailEvents result hsel htailTrace⟩
                    rw [htailEv, List.append_assoc]
                    rfl

theorem digestStringCorrect_proven :
    Models2Group4.DigestStringCorrect := by
  intro E W S Decoded Other ops kind string world
  refine ⟨?_, ?_, ?_⟩
  · intro result finalWorld events h
    obtain ⟨evs, hevs, htr⟩ := digestFromAbstractStringRun_trace ops kind string (world, [])
      (result, (finalWorld, events)) h
    dsimp only [List.nil_append] at hevs htr
    subst hevs
    exact htr
  · intro error finalWorld h
    change JuliaLean.base.loading.Models2Group4.digestFromAbstractStringRun ops kind string world = _
    rw [JuliaLean.base.loading.Models2Group4.digestFromAbstractStringRun.eq_def]
    unfold Models2Group4.observe at h
    rw [h]
    rfl
  · intro h
    change JuliaLean.base.loading.Models2Group4.digestFromAbstractStringRun ops kind string world = none
    rw [JuliaLean.base.loading.Models2Group4.digestFromAbstractStringRun.eq_def]
    unfold Models2Group4.observe at h
    rw [h]
    rfl

-- 4. loading-sha-parse
theorem parseDigestCorrect_proven :
    Models2Group4.ParseDigestCorrect := by
  intro E W S Decoded Other ops kind string world
  refine ⟨?_, ?_⟩
  · intro result finalWorld events h
    unfold JuliaLean.base.loading.Models2Group4.parseDigest
      JuliaLean.base.loading.Models2Group4.selectedDigestConstructor
      Models2Group4.traceDigestConstructor at h
    unfold Models2Group4.DigestParseTrace
    cases hsel : ops.selection kind string with
    | base =>
        rw [hsel] at h
        exact (digestStringCorrect_proven E W S Decoded Other ops.stringBody kind string world).1
          result finalWorld events h
    | custom =>
        rw [hsel, observe_recordResult] at h
        cases hcust : Models2Group4.observe (ops.custom kind string) world with
        | none => rw [hcust] at h; nomatch h
        | some p =>
            rcases p with ⟨res, fw⟩
            rw [hcust] at h
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            subst hres
            exact hev.symm
  · intro hsel
    unfold JuliaLean.base.loading.Models2Group4.parseDigest
      JuliaLean.base.loading.Models2Group4.selectedDigestConstructor
    rw [hsel]

-- 5. loading-sha-tryparse
private theorem argumentFilterInvariant_tryCatch {E W Other : Type}
    (act : Models2Group4.ObservationM E W (JuliaLean.base.loading.Models2Group4.DigestValue Other))
    (world : W) :
    Models2Group4.ArgumentFilterInvariant (Models2Group4.observe act world)
      (Models2Group4.observe
        (tryCatch act (fun (error : JuliaLean.base.loading.Models2Group4.DispatchError E) =>
          match error with
          | .argumentError _ => pure .nothing
          | _ => throw error)) world) := by
  unfold Models2Group4.ArgumentFilterInvariant
  rw [observe_tryCatch]
  cases h : Models2Group4.observe act world with
  | none =>
      exact And.intro Iff.rfl ⟨rfl, (fun _ _ hs => nomatch hs), (fun _ _ hs => nomatch hs),
        (fun _ _ hf => nomatch hf)⟩
  | some p =>
      rcases p with ⟨res, fw⟩
      cases res with
      | ok val =>
          dsimp only
          refine And.intro (Iff.intro ((fun hs => nomatch hs)) ((fun hf => nomatch hf)))
            ⟨rfl, ?_, (fun _ _ hs => nomatch hs), (fun _ _ hf => nomatch hf)⟩
          intro v w hs
          exact hs
      | error err =>
          cases err with
          | argumentError v =>
              dsimp only [observe_pure]
              refine And.intro (Iff.intro ((fun hs => nomatch hs)) ((fun hf => nomatch hf)))
                ⟨rfl, (fun _ _ hs => nomatch hs), ?_, (fun _ _ hf => nomatch hf)⟩
              intro e w hs
              cases hs
              exact ⟨fun _ => rfl, fun hnot => False.elim (hnot ⟨v, rfl⟩)⟩
          | ioError v =>
              dsimp only [observe_throw]
              refine And.intro (Iff.intro ((fun hs => nomatch hs)) ((fun hf => nomatch hf)))
                ⟨rfl, (fun _ _ hs => nomatch hs), ?_, ?_⟩
              · intro e w hs
                cases hs
                exact ⟨(fun ⟨_, harg⟩ => nomatch harg), fun _ => rfl⟩
              · intro e w hf ⟨_, harg⟩
                subst harg
                nomatch hf
          | typeError =>
              dsimp only [observe_throw]
              refine And.intro (Iff.intro ((fun hs => nomatch hs)) ((fun hf => nomatch hf)))
                ⟨rfl, (fun _ _ hs => nomatch hs), ?_, ?_⟩
              · intro e w hs
                cases hs
                exact ⟨(fun ⟨_, harg⟩ => nomatch harg), fun _ => rfl⟩
              · intro e w hf ⟨_, harg⟩
                subst harg
                nomatch hf
          | other v =>
              dsimp only [observe_throw]
              refine And.intro (Iff.intro ((fun hs => nomatch hs)) ((fun hf => nomatch hf)))
                ⟨rfl, (fun _ _ hs => nomatch hs), ?_, ?_⟩
              · intro e w hs
                cases hs
                exact ⟨(fun ⟨_, harg⟩ => nomatch harg), fun _ => rfl⟩
              · intro e w hf ⟨_, harg⟩
                subst harg
                nomatch hf

theorem tryParseDigestCorrect_proven :
    Models2Group4.TryParseDigestCorrect := by
  intro E W S Decoded Other ops kind string world
  refine ⟨argumentFilterInvariant_tryCatch _ world, ?_⟩
  intro result finalWorld events h
  unfold JuliaLean.base.loading.Models2Group4.tryParseDigest at h
  rw [observe_tryCatch] at h
  cases hsel : Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.selectedDigestParse
        (Models2Group4.traceDigestParse ops) kind string) (world, []) with
  | none => rw [hsel] at h; nomatch h
  | some p =>
      rcases p with ⟨original, w1, evs⟩
      rw [hsel] at h
      have htr : (match ops.selection kind string with
          | .base => Models2Group4.DigestParseTrace (ops.constructorOps.selection kind string)
              ops.constructorOps.stringBody.decodedStringSelection kind string evs original
          | .custom => evs = [.customParse kind string original]) := by
        unfold JuliaLean.base.loading.Models2Group4.selectedDigestParse
          Models2Group4.traceDigestParse at hsel
        cases hs : ops.selection kind string with
        | base =>
            rw [hs] at hsel
            exact (parseDigestCorrect_proven E W S Decoded Other ops.constructorOps kind string world).1
              original w1 evs hsel
        | custom =>
            rw [hs, observe_recordResult] at hsel
            cases hcust : Models2Group4.observe (ops.custom kind string) world with
            | none => rw [hcust] at hsel; nomatch hsel
            | some p2 =>
                rcases p2 with ⟨res2, fw2⟩
                rw [hcust] at hsel
                injection hsel with h1; injection h1 with hres2 h2; injection h2 with hfw2 hev2
                subst hres2
                exact hev2.symm
      have hfilter := argumentFilterInvariant_tryCatch
        (ExceptT.mk (StateT.mk (fun _ => some (original, w1))) : Models2Group4.ObservationM E W _) w1
      change Models2Group4.ArgumentFilterInvariant (some (original, w1)) _ at hfilter
      cases original with
      | ok val =>
          dsimp only [observe_pure] at h hfilter
          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
          subst hres hfw hev
          exact ⟨.ok val, htr, hfilter⟩
      | error err =>
          cases err <;>
          · dsimp only [observe_pure, observe_throw] at h hfilter
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            subst hres hfw hev
            exact ⟨.error _, htr, hfilter⟩

-- 6. loading-package-get
private theorem selectedPackageGetHere_diverges_none {E W P U Other : Type}
    (ops : JuliaLean.base.loading.Models2Group4.PackageHereDispatchOps (Models2Group4.ObservationM E W) P U Other)
    (projectFile : P) (name : JuliaLean.Strings.JStr) (world : W)
    (hdiv : match ops.selection projectFile name with
      | .base => Models2Group4.PackageHereDiverges ops.baseOps projectFile name world
      | .custom => Models2Group4.observe (ops.custom projectFile name) world = none) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.selectedPackageGetHere ops projectFile name) world = none := by
  unfold JuliaLean.base.loading.Models2Group4.selectedPackageGetHere
  cases hsel : ops.selection projectFile name with
  | custom => rw [hsel] at hdiv; exact hdiv
  | base =>
      rw [hsel] at hdiv
      unfold JuliaLean.base.loading.Models2Group4.packageGetHere
      rw [observe_bind]
      rcases hdiv with h1 | ⟨dep, w1, h1, h2⟩
      · rw [h1]
      · rw [h1]; exact h2

private theorem selectedPackageGetHere_spec {E W P U Other Proj CompareOther : Type}
    (ops : JuliaLean.base.loading.Models2Group4.PackageHereDispatchOps (Models2Group4.ObservationM E W) P U Other)
    (projectFile : P) (name : JuliaLean.Strings.JStr) (world : W)
    (evs : List (Models2Group4.PackageEvent E W P U Other Proj CompareOther)) :
    (∀ result finalWorld events,
      Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.selectedPackageGetHere
          (Models2Group4.tracePackageHereDispatch (Proj := Proj) (CompareOther := CompareOther) ops)
          projectFile name) (world, evs) = some (result, (finalWorld, events)) →
      ∃ suffix, events = evs ++ suffix ∧
        Models2Group4.PackageHereTrace (ops.selection projectFile name) projectFile name world result finalWorld suffix) ∧
    (Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.selectedPackageGetHere ops projectFile name) world = none ↔
      match ops.selection projectFile name with
      | .base => Models2Group4.PackageHereDiverges ops.baseOps projectFile name world
      | .custom => Models2Group4.observe (ops.custom projectFile name) world = none) := by
  refine And.intro ?_ (Iff.intro ?_ (selectedPackageGetHere_diverges_none ops projectFile name world))
  · intro result finalWorld events h
    unfold JuliaLean.base.loading.Models2Group4.selectedPackageGetHere
      Models2Group4.tracePackageHereDispatch at h
    unfold Models2Group4.PackageHereTrace
    cases hsel : ops.selection projectFile name with
    | custom =>
        rw [hsel, observe_recordPackageStep] at h
        cases hcust : Models2Group4.observe (ops.custom projectFile name) world with
        | none => rw [hcust] at h; nomatch h
        | some p =>
            rcases p with ⟨res, fw⟩
            rw [hcust] at h
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            subst hres hfw
            exact ⟨[.customHere projectFile name world res fw], hev.symm, rfl⟩
    | base =>
        rw [hsel] at h
        unfold JuliaLean.base.loading.Models2Group4.packageGetHere
          Models2Group4.tracePackageHere at h
        rw [observe_bind, observe_recordPackageStep] at h
        cases hdep : Models2Group4.observe (ops.baseOps.explicitProjectDepsGet projectFile name) world with
        | none => rw [hdep] at h; nomatch h
        | some p =>
            rcases p with ⟨res, w1⟩
            rw [hdep] at h
            cases res with
            | error err =>
                injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                subst hres hfw
                exact ⟨[.dependency projectFile name world (.error err) w1], hev.symm, Or.inl ⟨err, rfl, rfl⟩⟩
            | ok opt =>
                cases opt with
                | none =>
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    subst hres hfw
                    exact ⟨[.dependency projectFile name world (.ok none) w1], hev.symm,
                      Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl⟩)⟩
                | some dep =>
                    dsimp only at h
                    rw [observe_recordPackageStep] at h
                    cases hcon : Models2Group4.observe (ops.baseOps.constructPkgId dep name) w1 with
                    | none => rw [hcon] at h; nomatch h
                    | some p2 =>
                        rcases p2 with ⟨res2, w2⟩
                        rw [hcon] at h
                        injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                        subst hres hfw
                        refine ⟨[.dependency projectFile name world (.ok (some dep)) w1,
                          .construct dep name w1 res2 w2], ?_,
                          Or.inr (Or.inr ⟨dep, w1, rfl⟩)⟩
                        rw [← hev]; simp only [List.append_assoc]; rfl
  · intro hnone
    unfold JuliaLean.base.loading.Models2Group4.selectedPackageGetHere at hnone
    cases hsel : ops.selection projectFile name with
    | custom => rw [hsel] at hnone; exact hnone
    | base =>
        rw [hsel] at hnone
        unfold JuliaLean.base.loading.Models2Group4.packageGetHere at hnone
        rw [observe_bind] at hnone
        cases hdep : Models2Group4.observe (ops.baseOps.explicitProjectDepsGet projectFile name) world with
        | none => exact Or.inl hdep
        | some p =>
            rcases p with ⟨res, w1⟩
            rw [hdep] at hnone
            cases res with
            | error _ => nomatch hnone
            | ok opt =>
                cases opt with
                | none => nomatch hnone
                | some dep => exact Or.inr ⟨dep, w1, hdep, hnone⟩

theorem packageGetCorrect_proven :
    Models2Group4.PackageGetCorrect := by
  intro E W P U Other Proj CompareOther ops projectFile wherePkg name world
  dsimp only
  refine And.intro ?_ (Iff.intro ?_ ?_)
  · intro result finalWorld events h
    unfold JuliaLean.base.loading.Models2Group4.packageGet
      Models2Group4.tracePackageGet at h
    unfold Models2Group4.PackageGetTrace
    cases wherePkg with
    | none =>
        obtain ⟨suffix, hsuf, htr⟩ :=
          (selectedPackageGetHere_spec (Proj := Proj) (CompareOther := CompareOther)
            ops.here projectFile name world []).1 result finalWorld events h
        rw [List.nil_append] at hsuf
        subst hsuf
        exact htr
    | some context =>
        dsimp only at h ⊢
        rw [observe_bind, observe_recordPackageStep] at h
        cases hid : Models2Group4.observe
            (ops.projectFileNameUuid projectFile ⟨context.value.name, context.nameSmall⟩) world with
        | none => rw [hid] at h; nomatch h
        | some p =>
            rcases p with ⟨res, w1⟩
            rw [hid] at h
            cases res with
            | error err =>
                injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                subst hres hfw
                exact Or.inl ⟨err, hev.symm, rfl⟩
            | ok project =>
                dsimp only at h
                rw [observe_bind, observe_recordPackageStep] at h
                cases hcmp : Models2Group4.observe (ops.notEqual project context.value) w1 with
                | none => rw [hcmp] at h; nomatch h
                | some p2 =>
                    rcases p2 with ⟨compared, w2⟩
                    rw [hcmp] at h
                    cases compared with
                    | error err =>
                        injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                        subst hres hfw
                        exact Or.inr ⟨project, w1, .error err, w2, [], hev.symm, rfl, rfl, rfl⟩
                    | ok cmpVal =>
                        cases cmpVal with
                        | other v =>
                            dsimp only [observe_throw] at h
                            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                            subst hres hfw
                            exact Or.inr ⟨project, w1, .ok (.other v), w2, [], hev.symm, rfl, rfl, rfl⟩
                        | bool b =>
                            cases b with
                            | true =>
                                dsimp only [observe_pure] at h
                                injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                subst hres hfw
                                exact Or.inr ⟨project, w1, .ok (.bool true), w2, [], hev.symm, rfl, rfl, rfl⟩
                            | false =>
                                dsimp only at h
                                obtain ⟨suffix, hsuf, htr⟩ :=
                                  (selectedPackageGetHere_spec (Proj := Proj) (CompareOther := CompareOther)
                                    ops.here projectFile name w2
                                    [.identity projectFile ⟨context.value.name, context.nameSmall⟩ world (.ok project) w1,
                                     .compare project context.value w1 (.ok (.bool false)) w2]).1
                                    result finalWorld events h
                                exact Or.inr ⟨project, w1, .ok (.bool false), w2, suffix, hsuf, htr⟩
  · intro hnone
    unfold JuliaLean.base.loading.Models2Group4.packageGet at hnone
    cases wherePkg with
    | none =>
        exact (selectedPackageGetHere_spec (Proj := Proj) (CompareOther := CompareOther)
          ops.here projectFile name world []).2.mp hnone
    | some context =>
        dsimp only at hnone ⊢
        rw [observe_bind] at hnone
        cases hid : Models2Group4.observe
            (ops.projectFileNameUuid projectFile ⟨context.value.name, context.nameSmall⟩) world with
        | none => exact Or.inl rfl
        | some p =>
            rcases p with ⟨res, w1⟩
            rw [hid] at hnone
            cases res with
            | error _ => nomatch hnone
            | ok project =>
                dsimp only at hnone
                rw [observe_bind] at hnone
                cases hcmp : Models2Group4.observe (ops.notEqual project context.value) w1 with
                | none => exact Or.inr ⟨project, w1, rfl, Or.inl hcmp⟩
                | some p2 =>
                    rcases p2 with ⟨compared, w2⟩
                    rw [hcmp] at hnone
                    cases compared with
                    | error _ => nomatch hnone
                    | ok cmpVal =>
                        cases cmpVal with
                        | other _ => nomatch hnone
                        | bool b =>
                            cases b with
                            | true => nomatch hnone
                            | false =>
                                exact Or.inr ⟨project, w1, rfl, Or.inr ⟨w2, hcmp,
                                  (selectedPackageGetHere_spec (Proj := Proj) (CompareOther := CompareOther)
                                    ops.here projectFile name w2 []).2.mp hnone⟩⟩
  · intro hdiv
    unfold JuliaLean.base.loading.Models2Group4.packageGet
    cases wherePkg with
    | none =>
        exact selectedPackageGetHere_diverges_none ops.here projectFile name world hdiv
    | some context =>
        dsimp only at hdiv ⊢
        rw [observe_bind]
        rcases hdiv with hid | ⟨project, w1, hid, h2⟩
        · rw [hid]
        · rw [hid]
          dsimp only
          rw [observe_bind]
          rcases h2 with hcmp | ⟨w2, hcmp, h3⟩
          · rw [hcmp]
          · rw [hcmp]
            exact selectedPackageGetHere_diverges_none ops.here projectFile name w2 h3

-- 7. loading-find-source-file
private theorem findSource_diverges_none {E W S Joined PredicateOther ResultOther : Type}
    (ops : JuliaLean.base.loading.Models2Group4.FindSourceOps (Models2Group4.ObservationM E W) S Joined PredicateOther ResultOther)
    (path : S) (world : W)
    (hdiv : Models2Group4.FindSourceDiverges ops path world) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.findSourceFile (E := E) ops path) world = none := by
  unfold JuliaLean.base.loading.Models2Group4.findSourceFile
  rcases hdiv with ⟨pt, bef, hreach, hnone⟩
  cases hreach with
  | start =>
      dsimp only at hnone
      rw [observe_bind, hnone]
  | pathFile w1 habs =>
      dsimp only at hnone
      rw [observe_bind, habs]
      dsimp only
      rw [observe_bind, hnone]
  | joinPath w1 w2 h1 hpath =>
      cases h1 with
      | pathFile _ habs =>
          dsimp only at hnone
          rw [observe_bind, habs]
          dsimp only
          rw [observe_bind, hpath]
          dsimp only
          rw [observe_bind, hnone]
  | joinedFile w2 w3 joined h2 hjoin =>
      cases h2 with
      | joinPath w1 _ h1 hpath =>
          cases h1 with
          | pathFile _ habs =>
              dsimp only at hnone
              rw [observe_bind, habs]
              dsimp only
              rw [observe_bind, hpath]
              dsimp only
              rw [observe_bind, hjoin]
              dsimp only
              rw [observe_bind, hnone]
  | normalize w3 w4 joined h3 hfound =>
      cases h3 with
      | joinedFile w2 _ _ h2 hjoin =>
          cases h2 with
          | joinPath w1 _ h1 hpath =>
              cases h1 with
              | pathFile _ habs =>
                  dsimp only at hnone
                  rw [observe_bind, habs]
                  dsimp only
                  rw [observe_bind, hpath]
                  dsimp only
                  rw [observe_bind, hjoin]
                  dsimp only
                  rw [observe_bind, hfound]
                  exact hnone

private theorem findSourceFile_main {E W S Joined PredicateOther ResultOther : Type}
    (ops : JuliaLean.base.loading.Models2Group4.FindSourceOps (Models2Group4.ObservationM E W) S Joined PredicateOther ResultOther)
    (path : S) (world : W) :
    let traced := Models2Group4.observe (JuliaLean.base.loading.Models2Group4.findSourceFile (E := E) (Models2Group4.traceFindSource ops) path) (world, [])
    let plain := Models2Group4.observe (JuliaLean.base.loading.Models2Group4.findSourceFile (E := E) ops path) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result finalWorld events,
      traced = some (result, (finalWorld, events)) →
      Models2Group4.FindSourceTrace ops.bindir ops.datarootdir path world result finalWorld events) ∧
    (plain = none → Models2Group4.FindSourceDiverges ops path world) := by
  dsimp only
  unfold JuliaLean.base.loading.Models2Group4.findSourceFile
    Models2Group4.traceFindSource Models2Group4.FindSourceDiverges
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  cases habs : Models2Group4.observe (ops.isabspath path) world with
  | none =>
      exact ⟨rfl, (fun _ _ _ h => nomatch h), fun _ => ⟨.absolute, world, .start, habs⟩⟩
  | some p1 =>
      rcases p1 with ⟨res1, w1⟩
      cases res1 with
      | error err =>
          refine ⟨rfl, ?_, (fun h => nomatch h)⟩
          intro result finalWorld events h
          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
          subst hres hfw
          rw [hev.symm]
          exact .absoluteError world w1 err
      | ok v1 =>
          cases v1 with
          | other u =>
              dsimp only [observe_throw]
              refine ⟨rfl, ?_, (fun h => nomatch h)⟩
              intro result finalWorld events h
              injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
              subst hres hfw
              rw [hev.symm]
              exact .absoluteNonBool world w1 u
          | bool b1 =>
              cases b1 with
              | true =>
                  dsimp only [observe_pure]
                  refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                  intro result finalWorld events h
                  injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                  subst hres hfw
                  rw [hev.symm]
                  exact .absoluteTrue world w1
              | false =>
                  dsimp only
                  rw [observe_bind, observe_bind, observe_recordPackageStep]
                  cases hpath : Models2Group4.observe (ops.isfilePath path) w1 with
                  | none =>
                      dsimp only
                      exact ⟨rfl, (fun _ _ _ h => nomatch h),
                        fun _ => ⟨.pathFile, w1, .pathFile w1 habs, hpath⟩⟩
                  | some p2 =>
                      rcases p2 with ⟨res2, w2⟩
                      cases res2 with
                      | error err =>
                          refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                          intro result finalWorld events h
                          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                          subst hres hfw
                          rw [hev.symm]
                          exact .pathError world w1 w2 err
                      | ok v2 =>
                          cases v2 with
                          | other u =>
                              dsimp only [observe_throw]
                              refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                              intro result finalWorld events h
                              injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                              subst hres hfw
                              rw [hev.symm]
                              exact .pathNonBool world w1 w2 u
                          | bool b2 =>
                              cases b2 with
                              | true =>
                                  dsimp only [observe_pure]
                                  refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                  intro result finalWorld events h
                                  injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                  subst hres hfw
                                  rw [hev.symm]
                                  exact .pathTrue world w1 w2
                              | false =>
                                  dsimp only
                                  rw [observe_bind, observe_bind, observe_recordPackageStep]
                                  cases hjoin : Models2Group4.observe
                                      (ops.joinpath ops.bindir ops.datarootdir
                                        JuliaLean.base.loading.Models2Group4.findSourceJuliaLiteral
                                        JuliaLean.base.loading.Models2Group4.findSourceBaseLiteral path) w2 with
                                  | none =>
                                      dsimp only
                                      exact ⟨rfl, (fun _ _ _ h => nomatch h),
                                        fun _ => ⟨.joinPath, w2, .joinPath w1 w2 (.pathFile w1 habs) hpath, hjoin⟩⟩
                                  | some p3 =>
                                      rcases p3 with ⟨res3, w3⟩
                                      cases res3 with
                                      | error err =>
                                          refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                          intro result finalWorld events h
                                          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                          subst hres hfw
                                          rw [hev.symm]
                                          exact .joinError world w1 w2 w3 err _ _ rfl rfl
                                      | ok joined =>
                                          dsimp only
                                          rw [observe_bind, observe_bind, observe_recordPackageStep]
                                          cases hfound : Models2Group4.observe (ops.isfileJoined joined) w3 with
                                          | none =>
                                              dsimp only
                                              exact ⟨rfl, (fun _ _ _ h => nomatch h),
                                                fun _ => ⟨.joinedFile joined, w3,
                                                  .joinedFile w2 w3 joined (.joinPath w1 w2 (.pathFile w1 habs) hpath) hjoin,
                                                  hfound⟩⟩
                                          | some p4 =>
                                              rcases p4 with ⟨res4, w4⟩
                                              cases res4 with
                                              | error err =>
                                                  refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                                  intro result finalWorld events h
                                                  injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                                  subst hres hfw
                                                  rw [hev.symm]
                                                  exact .joinedError world w1 w2 w3 w4 joined err _ _ rfl rfl
                                              | ok v4 =>
                                                  cases v4 with
                                                  | other u =>
                                                      dsimp only [observe_throw]
                                                      refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                                      intro result finalWorld events h
                                                      injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                                      subst hres hfw
                                                      rw [hev.symm]
                                                      exact .joinedNonBool world w1 w2 w3 w4 joined u _ _ rfl rfl
                                                  | bool b4 =>
                                                      cases b4 with
                                                      | false =>
                                                          dsimp only [observe_pure]
                                                          refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                                          intro result finalWorld events h
                                                          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                                          subst hres hfw
                                                          rw [hev.symm]
                                                          exact .joinedFalse world w1 w2 w3 w4 joined _ _ rfl rfl
                                                      | true =>
                                                          dsimp only
                                                          rw [observe_recordPackageStep]
                                                          cases hnorm : Models2Group4.observe (ops.normpath joined) w4 with
                                                          | none =>
                                                              dsimp only
                                                              exact ⟨rfl, (fun _ _ _ h => nomatch h),
                                                                fun _ => ⟨.normalize joined, w4,
                                                                  .normalize w3 w4 joined
                                                                    (.joinedFile w2 w3 joined
                                                                      (.joinPath w1 w2 (.pathFile w1 habs) hpath) hjoin) hfound,
                                                                  hnorm⟩⟩
                                                          | some p5 =>
                                                              rcases p5 with ⟨res5, w5⟩
                                                              refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                                              intro result finalWorld events h
                                                              injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                                              subst hres hfw
                                                              rw [hev.symm]
                                                              exact .normalized world w1 w2 w3 w4 w5 joined res5 _ _ rfl rfl

theorem findSourceFileCorrect_proven :
    Models2Group4.FindSourceFileCorrect := by
  refine ⟨rfl, rfl, ?_⟩
  intro E W S Joined PredicateOther ResultOther ops path world
  have hm := findSourceFile_main ops path world
  exact And.intro hm.1 (And.intro hm.2.1 (Iff.intro hm.2.2 (findSource_diverges_none ops path world)))

-- 8. loading-sort-by
theorem sortByCorrect_proven :
    Models2Group4.SortByCorrect := by
  intro W L I ops otherCore paths pkgimages index world
  refine And.intro ?_ (Iff.intro ?_ ?_)
  · intro result finalWorld events h
    unfold JuliaLean.base.loading.Models2Group4.sortBy
      Models2Group4.traceSortBy at h
    unfold Models2Group4.SortByTrace
    dsimp only at h
    rw [observe_bind, observe_recordPackageStep] at h
    cases hpkg : Models2Group4.observe (ops.pkgimagesGetindex pkgimages index) world with
    | none => rw [hpkg] at h; nomatch h
    | some p1 =>
        rcases p1 with ⟨res1, w1⟩
        rw [hpkg] at h
        cases res1 with
        | error err =>
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            subst hres hfw
            exact Or.inl ⟨err, hev.symm, rfl⟩
        | ok image =>
            dsimp only at h
            rw [observe_bind, observe_recordPackageStep] at h
            cases hpath : Models2Group4.observe (ops.pathsGetindex paths index) w1 with
            | none => rw [hpath] at h; nomatch h
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                rw [hpath] at h
                cases res2 with
                | error err =>
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    subst hres hfw
                    exact Or.inr (Or.inl ⟨image, w1, err, hev.symm, rfl⟩)
                | ok path =>
                    dsimp only at h
                    rw [observe_bind, observe_recordPackageStep] at h
                    cases hmtime : Models2Group4.observe (ops.mtime path) w2 with
                    | none => rw [hmtime] at h; nomatch h
                    | some p3 =>
                        rcases p3 with ⟨res3, w3⟩
                        rw [hmtime] at h
                        cases res3 with
                        | error err =>
                            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                            subst hres hfw
                            exact Or.inr (Or.inr (Or.inl ⟨image, w1, path, w2, err, hev.symm, rfl⟩))
                        | ok modified =>
                            dsimp only at h
                            unfold JuliaLean.base.boot.NamedTuple_names at h
                            unfold Models2Group4.SortByConstructionTrace
                            rw [observe_liftCoreAction] at h
                            unfold Models2Group4.recordSortCoreStep at h
                            dsimp only [Bind.bind, Option.bind, Pure.pure,
                              JuliaLean.base.boot.tupleV, JuliaLean.base.boot.coreV] at h ⊢
                            let names := JuliaLean.base.expr.Value.leaf
                              (ops.core.tuple [.symbol "pkgimage", .symbol "mtime"])
                            let values := JuliaLean.base.expr.Value.leaf
                              (ops.core.tuple [image, modified])
                            let head := JuliaLean.base.expr.Value.leaf (ops.core.core "NamedTuple")
                            let parameters := [names, JuliaLean.base.expr.Value.leaf (ops.core.typeOf values)]
                            cases happ : ops.core.applyType head parameters w3 with
                            | none => rw [happ] at h; nomatch h
                            | some p4 =>
                                rw [happ] at h
                                cases p4 with
                                | error ep =>
                                    rcases ep with ⟨err, w4⟩
                                    dsimp only at h
                                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                    subst hres hfw
                                    refine Or.inr (Or.inr (Or.inr ⟨image, w1, path, w2, modified, w3,
                                      [.applyType head parameters w3 (.error err) w4], ?_,
                                      Or.inl ⟨err, rfl, rfl⟩⟩))
                                    rw [← hev]; simp only [List.append_assoc]; rfl
                                | ok op =>
                                    rcases op with ⟨target, w4⟩
                                    dsimp only at h
                                    cases hsplat : ops.core.splatnew target values w4 with
                                    | none => rw [hsplat] at h; nomatch h
                                    | some p5 =>
                                        rw [hsplat] at h
                                        cases p5 with
                                        | error ep =>
                                            rcases ep with ⟨err, w5⟩
                                            dsimp only at h
                                            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                            subst hres hfw
                                            refine Or.inr (Or.inr (Or.inr ⟨image, w1, path, w2, modified, w3,
                                              [.applyType head parameters w3 (.ok target) w4,
                                               .splatnew target values w4 (.error err) w5], ?_,
                                              Or.inr ⟨target, w4, .error err, rfl, rfl⟩⟩))
                                            rw [← hev]; simp only [List.append_assoc]; rfl
                                        | ok op2 =>
                                            rcases op2 with ⟨val, w5⟩
                                            dsimp only at h
                                            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                            subst hres hfw
                                            refine Or.inr (Or.inr (Or.inr ⟨image, w1, path, w2, modified, w3,
                                              [.applyType head parameters w3 (.ok target) w4,
                                               .splatnew target values w4 (.ok val) w5], ?_,
                                              Or.inr ⟨target, w4, .ok val, rfl, rfl⟩⟩))
                                            rw [← hev]; simp only [List.append_assoc]; rfl
  · intro hnone
    unfold JuliaLean.base.loading.Models2Group4.sortBy at hnone
    rw [observe_bind] at hnone
    cases hpkg : Models2Group4.observe (ops.pkgimagesGetindex pkgimages index) world with
    | none => exact Or.inl rfl
    | some p1 =>
        rcases p1 with ⟨res1, w1⟩
        rw [hpkg] at hnone
        cases res1 with
        | error _ => nomatch hnone
        | ok image =>
            dsimp only at hnone
            rw [observe_bind] at hnone
            cases hpath : Models2Group4.observe (ops.pathsGetindex paths index) w1 with
            | none => exact Or.inr ⟨image, w1, rfl, Or.inl hpath⟩
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                rw [hpath] at hnone
                cases res2 with
                | error _ => nomatch hnone
                | ok path =>
                    dsimp only at hnone
                    rw [observe_bind] at hnone
                    cases hmtime : Models2Group4.observe (ops.mtime path) w2 with
                    | none => exact Or.inr ⟨image, w1, rfl, Or.inr ⟨path, w2, hpath, Or.inl hmtime⟩⟩
                    | some p3 =>
                        rcases p3 with ⟨res3, w3⟩
                        rw [hmtime] at hnone
                        cases res3 with
                        | error _ => nomatch hnone
                        | ok modified =>
                            dsimp only at hnone
                            unfold JuliaLean.base.boot.NamedTuple_names at hnone
                            unfold Models2Group4.SortByConstructionDiverges
                            rw [observe_liftCoreAction] at hnone
                            dsimp only [Bind.bind, Option.bind, Pure.pure,
                              JuliaLean.base.boot.tupleV, JuliaLean.base.boot.coreV] at hnone ⊢
                            let names := JuliaLean.base.expr.Value.leaf
                              (ops.core.tuple [.symbol "pkgimage", .symbol "mtime"])
                            let values := JuliaLean.base.expr.Value.leaf
                              (ops.core.tuple [image, modified])
                            let head := JuliaLean.base.expr.Value.leaf (ops.core.core "NamedTuple")
                            let parameters := [names, JuliaLean.base.expr.Value.leaf (ops.core.typeOf values)]
                            cases happ : ops.core.applyType head parameters w3 with
                            | none =>
                                exact Or.inr ⟨image, w1, rfl,
                                  Or.inr ⟨path, w2, hpath, Or.inr ⟨modified, w3, hmtime, Or.inl happ⟩⟩⟩
                            | some p4 =>
                                rw [happ] at hnone
                                cases p4 with
                                | error _ => nomatch hnone
                                | ok op =>
                                    rcases op with ⟨target, w4⟩
                                    dsimp only at hnone
                                    cases hsplat : ops.core.splatnew target values w4 with
                                    | none =>
                                        exact Or.inr ⟨image, w1, rfl,
                                          Or.inr ⟨path, w2, hpath,
                                            Or.inr ⟨modified, w3, hmtime, Or.inr ⟨target, w4, happ, hsplat⟩⟩⟩⟩
                                    | some p5 =>
                                        rw [hsplat] at hnone
                                        cases p5 <;> nomatch hnone
  · intro hdiv
    unfold JuliaLean.base.loading.Models2Group4.sortBy
    rw [observe_bind]
    rcases hdiv with hpkg | ⟨image, w1, hpkg, h2⟩
    · rw [hpkg]
    · rw [hpkg]
      dsimp only
      rw [observe_bind]
      rcases h2 with hpath | ⟨path, w2, hpath, h3⟩
      · rw [hpath]
      · rw [hpath]
        dsimp only
        rw [observe_bind]
        rcases h3 with hmtime | ⟨modified, w3, hmtime, h4⟩
        · rw [hmtime]
        · rw [hmtime]
          dsimp only
          unfold JuliaLean.base.boot.NamedTuple_names
          unfold Models2Group4.SortByConstructionDiverges at h4
          rw [observe_liftCoreAction]
          dsimp only [Bind.bind, Option.bind, Pure.pure,
            JuliaLean.base.boot.tupleV, JuliaLean.base.boot.coreV] at h4 ⊢
          rcases h4 with happ | ⟨target, w4, happ, hsplat⟩
          · rw [happ]
          · rw [happ]; dsimp only; rw [hsplat]

-- 9. loading-sort-lt
private theorem sortLtBranch_spec {E W V Other : Type}
    (ops : JuliaLean.base.loading.Models2Group4.SortLtOps (Models2Group4.ObservationM E W) V Other)
    (a b : V) (field : JuliaLean.base.loading.Models2Group4.SortProperty)
    (w : W) (evs : List (Models2Group4.SortLtEvent E W V Other)) :
    (∀ result finalWorld events,
      Models2Group4.observe (do
        let left ← (Models2Group4.traceSortLt ops).getproperty a field
        let right ← (Models2Group4.traceSortLt ops).getproperty b field
        (Models2Group4.traceSortLt ops).lessThan left right) (w, evs) =
        some (result, (finalWorld, events)) →
      ∃ suffix, events = evs ++ suffix ∧
        Models2Group4.SortLtBranchTrace a b field w result finalWorld suffix) ∧
    (Models2Group4.observe (do
        let left ← ops.getproperty a field
        let right ← ops.getproperty b field
        ops.lessThan left right) w = none ↔
      Models2Group4.SortLtBranchDiverges ops a b field w) := by
  refine And.intro ?_ (Iff.intro ?_ ?_)
  · intro result finalWorld events h
    dsimp only [Models2Group4.traceSortLt] at h
    unfold Models2Group4.SortLtBranchTrace
    rw [observe_bind, observe_recordPackageStep] at h
    cases ha : Models2Group4.observe (ops.getproperty a field) w with
    | none => rw [ha] at h; nomatch h
    | some p1 =>
        rcases p1 with ⟨res1, w1⟩
        rw [ha] at h
        cases res1 with
        | error err =>
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            subst hres hfw
            exact ⟨[.property a field w (.error err) w1], hev.symm, Or.inl ⟨err, rfl, rfl⟩⟩
        | ok left =>
            dsimp only at h
            rw [observe_bind, observe_recordPackageStep] at h
            cases hb : Models2Group4.observe (ops.getproperty b field) w1 with
            | none => rw [hb] at h; nomatch h
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                rw [hb] at h
                cases res2 with
                | error err =>
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    subst hres hfw
                    refine ⟨[.property a field w (.ok left) w1,
                      .property b field w1 (.error err) w2], ?_,
                      Or.inr (Or.inl ⟨left, w1, err, rfl, rfl⟩)⟩
                    rw [← hev]; simp only [List.append_assoc]; rfl
                | ok right =>
                    dsimp only at h
                    rw [observe_recordPackageStep] at h
                    cases hlt : Models2Group4.observe (ops.lessThan left right) w2 with
                    | none => rw [hlt] at h; nomatch h
                    | some p3 =>
                        rcases p3 with ⟨res3, w3⟩
                        rw [hlt] at h
                        injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                        subst hres hfw
                        refine ⟨[.property a field w (.ok left) w1,
                          .property b field w1 (.ok right) w2,
                          .less left right w2 res3 w3], ?_,
                          Or.inr (Or.inr ⟨left, w1, right, w2, rfl⟩)⟩
                        rw [← hev]; simp only [List.append_assoc]; rfl
  · intro hnone
    unfold Models2Group4.SortLtBranchDiverges
    rw [observe_bind] at hnone
    cases ha : Models2Group4.observe (ops.getproperty a field) w with
    | none => exact Or.inl rfl
    | some p1 =>
        rcases p1 with ⟨res1, w1⟩
        rw [ha] at hnone
        cases res1 with
        | error _ => nomatch hnone
        | ok left =>
            dsimp only at hnone
            rw [observe_bind] at hnone
            cases hb : Models2Group4.observe (ops.getproperty b field) w1 with
            | none => exact Or.inr ⟨left, w1, rfl, Or.inl hb⟩
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                rw [hb] at hnone
                cases res2 with
                | error _ => nomatch hnone
                | ok right => exact Or.inr ⟨left, w1, rfl, Or.inr ⟨right, w2, hb, hnone⟩⟩
  · intro hdiv
    unfold Models2Group4.SortLtBranchDiverges at hdiv
    rw [observe_bind]
    rcases hdiv with ha | ⟨left, w1, ha, h2⟩
    · rw [ha]
    · rw [ha]
      dsimp only
      rw [observe_bind]
      rcases h2 with hb | ⟨right, w2, hb, hlt⟩
      · rw [hb]
      · rw [hb]; exact hlt

theorem sortLtCorrect_proven :
    Models2Group4.SortLtCorrect := by
  intro E W V Other ops a b world
  refine And.intro ?_ (Iff.intro ?_ ?_)
  · intro result finalWorld events h
    unfold JuliaLean.base.loading.Models2Group4.sortLt at h
    unfold Models2Group4.SortLtTrace
    dsimp only [Models2Group4.traceSortLt] at h
    rw [observe_bind, observe_recordPackageStep] at h
    cases ha : Models2Group4.observe (ops.getproperty a .pkgimage) world with
    | none => rw [ha] at h; nomatch h
    | some p1 =>
        rcases p1 with ⟨res1, w1⟩
        rw [ha] at h
        cases res1 with
        | error err =>
            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
            subst hres hfw
            exact Or.inl ⟨err, hev.symm, rfl⟩
        | ok left =>
            dsimp only at h
            rw [observe_bind, observe_recordPackageStep] at h
            cases hb : Models2Group4.observe (ops.getproperty b .pkgimage) w1 with
            | none => rw [hb] at h; nomatch h
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                rw [hb] at h
                cases res2 with
                | error err =>
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    subst hres hfw
                    exact Or.inr (Or.inl ⟨left, w1, err, hev.symm, rfl⟩)
                | ok right =>
                    dsimp only at h
                    rw [observe_bind, observe_recordPackageStep] at h
                    cases hdiff : Models2Group4.observe (ops.notEqual left right) w2 with
                    | none => rw [hdiff] at h; nomatch h
                    | some p3 =>
                        rcases p3 with ⟨compared, w3⟩
                        rw [hdiff] at h
                        cases compared with
                        | error err =>
                            injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                            subst hres hfw
                            exact Or.inr (Or.inr ⟨left, w1, right, w2, .error err, w3, [], hev.symm, rfl, rfl, rfl⟩)
                        | ok cmpVal =>
                            cases cmpVal with
                            | other u =>
                                dsimp only [observe_throw] at h
                                injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                subst hres hfw
                                exact Or.inr (Or.inr ⟨left, w1, right, w2, .ok (.other u), w3, [], hev.symm, rfl, rfl, rfl⟩)
                            | bool flag =>
                                cases flag with
                                | true =>
                                    dsimp only at h
                                    obtain ⟨suffix, hsuf, htr⟩ :=
                                      (sortLtBranch_spec ops a b .pkgimage w3
                                        [.property a .pkgimage world (.ok left) w1,
                                         .property b .pkgimage w1 (.ok right) w2,
                                         .different left right w2 (.ok (.bool true)) w3]).1
                                        result finalWorld events h
                                    exact Or.inr (Or.inr ⟨left, w1, right, w2, .ok (.bool true), w3, suffix, hsuf, htr⟩)
                                | false =>
                                    dsimp only at h
                                    obtain ⟨suffix, hsuf, htr⟩ :=
                                      (sortLtBranch_spec ops a b .mtime w3
                                        [.property a .pkgimage world (.ok left) w1,
                                         .property b .pkgimage w1 (.ok right) w2,
                                         .different left right w2 (.ok (.bool false)) w3]).1
                                        result finalWorld events h
                                    exact Or.inr (Or.inr ⟨left, w1, right, w2, .ok (.bool false), w3, suffix, hsuf, htr⟩)
  · intro hnone
    unfold JuliaLean.base.loading.Models2Group4.sortLt at hnone
    rw [observe_bind] at hnone
    cases ha : Models2Group4.observe (ops.getproperty a .pkgimage) world with
    | none => exact Or.inl rfl
    | some p1 =>
        rcases p1 with ⟨res1, w1⟩
        rw [ha] at hnone
        cases res1 with
        | error _ => nomatch hnone
        | ok left =>
            dsimp only at hnone
            rw [observe_bind] at hnone
            cases hb : Models2Group4.observe (ops.getproperty b .pkgimage) w1 with
            | none => exact Or.inr ⟨left, w1, rfl, Or.inl hb⟩
            | some p2 =>
                rcases p2 with ⟨res2, w2⟩
                rw [hb] at hnone
                cases res2 with
                | error _ => nomatch hnone
                | ok right =>
                    dsimp only at hnone
                    rw [observe_bind] at hnone
                    cases hdiff : Models2Group4.observe (ops.notEqual left right) w2 with
                    | none => exact Or.inr ⟨left, w1, rfl, Or.inr ⟨right, w2, hb, Or.inl hdiff⟩⟩
                    | some p3 =>
                        rcases p3 with ⟨compared, w3⟩
                        rw [hdiff] at hnone
                        cases compared with
                        | error _ => nomatch hnone
                        | ok cmpVal =>
                            cases cmpVal with
                            | other _ => nomatch hnone
                            | bool flag =>
                                cases flag with
                                | true =>
                                    exact Or.inr ⟨left, w1, rfl, Or.inr ⟨right, w2, hb,
                                      Or.inr ⟨true, w3, hdiff,
                                        (sortLtBranch_spec ops a b .pkgimage w3 []).2.mp hnone⟩⟩⟩
                                | false =>
                                    exact Or.inr ⟨left, w1, rfl, Or.inr ⟨right, w2, hb,
                                      Or.inr ⟨false, w3, hdiff,
                                        (sortLtBranch_spec ops a b .mtime w3 []).2.mp hnone⟩⟩⟩
  · intro hdiv
    unfold JuliaLean.base.loading.Models2Group4.sortLt
    rw [observe_bind]
    rcases hdiv with ha | ⟨left, w1, ha, h2⟩
    · rw [ha]
    · rw [ha]
      dsimp only
      rw [observe_bind]
      rcases h2 with hb | ⟨right, w2, hb, h3⟩
      · rw [hb]
      · rw [hb]
        dsimp only
        rw [observe_bind]
        rcases h3 with hdiff | ⟨flag, w3, hdiff, h4⟩
        · rw [hdiff]
        · rw [hdiff]
          cases flag with
          | true => exact (sortLtBranch_spec ops a b .pkgimage w3 []).2.mpr h4
          | false => exact (sortLtBranch_spec ops a b .mtime w3 []).2.mpr h4

-- 10. loading-cache-flags-uint8
private def expectedFlagByteFields (flags : JInt .u8) :
    JuliaLean.base.loading.Models2Group4.FlagByteFields where
  usePkgimages := decide (flags.val % 2 = 1)
  debugLevel := JuliaLean.base.int.band
    (JuliaLean.base.int.widenTo .i64
      (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 1)))
    (JuliaLean.base.int.lit .i64 3)
  checkBounds := JuliaLean.base.int.band
    (JuliaLean.base.int.widenTo .i64
      (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 3)))
    (JuliaLean.base.int.lit .i64 3)
  inlineValue := decide ((flags.val / 32) % 2 = 1)
  optLevel := JuliaLean.base.int.band
    (JuliaLean.base.int.widenTo .i64
      (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 6)))
    (JuliaLean.base.int.lit .i64 3)

private theorem decodeCacheFlagByte_eq (flags : JInt .u8) :
    JuliaLean.base.loading.Models2Group4.decodeCacheFlagByte flags =
      .ok (expectedFlagByteFields flags) := by
  unfold JuliaLean.base.loading.Models2Group4.decodeCacheFlagByte expectedFlagByteFields
  have hflags := flags.property
  have hbit0 : (JuliaLean.base.int.band (JuliaLean.base.int.widenTo .i64 flags)
      (JuliaLean.base.int.lit .i64 1)).val = flags.val % 2 := band_widen_u8_one_val flags
  have hshr5 : (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 5)).val =
      flags.val / 32 := by
    have h5 : (JuliaLean.base.int.lit .i64 5).val = 5 := wrap_i64_five
    rw [shr_u8_val flags _ (by rw [h5]; omega), h5]
    rfl
  have hbit5 : (JuliaLean.base.int.band
      (JuliaLean.base.int.widenTo .i64
        (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 5)))
      (JuliaLean.base.int.lit .i64 1)).val = (flags.val / 32) % 2 := by
    rw [band_widen_u8_one_val, hshr5]
  rw [boolFromReal_bit _ (hbit0 ▸ mod_two_zero_or_one flags.val), boolFromReal_bit _ (hbit5 ▸ mod_two_zero_or_one (flags.val / 32)),
    convert_i64_self, convert_i64_self, convert_i64_self, hbit0, hbit5]
  rfl

private theorem int_byte_digits_sum (x : Int) (hx : 0 ≤ x ∧ x ≤ 255) :
    x = (if decide (x % 2 = 1) = true then 1 else 0) + 2 * ((x / 2) % 4) +
      8 * ((x / 8) % 4) + (if decide ((x / 32) % 2 = 1) = true then 32 else 0) +
      64 * ((x / 64) % 4) := by
  by_cases hb0 : x % 2 = 1 <;> by_cases hb5 : (x / 32) % 2 = 1 <;>
    simp only [hb0, hb5, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> omega

private theorem expectedFlagByteFields_digits (flags : JInt .u8) :
    Models2Group4.FlagByteDigits flags (expectedFlagByteFields flags) := by
  unfold Models2Group4.FlagByteDigits expectedFlagByteFields
  dsimp only
  have hflags : 0 ≤ flags.val ∧ flags.val ≤ 255 := flags.property
  have hshr1 : (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 1)).val =
      flags.val / 2 := by
    have h1 : (JuliaLean.base.int.lit .i64 1).val = 1 := wrap_i64_one
    rw [shr_u8_val flags _ (by rw [h1]; omega), h1]
    rfl
  have hshr3 : (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 3)).val =
      flags.val / 8 := by
    have h3 : (JuliaLean.base.int.lit .i64 3).val = 3 := wrap_i64_three
    rw [shr_u8_val flags _ (by rw [h3]; omega), h3]
    rfl
  have hshr6 : (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 6)).val =
      flags.val / 64 := by
    have h6 : (JuliaLean.base.int.lit .i64 6).val = 6 := wrap_i64_six
    rw [shr_u8_val flags _ (by rw [h6]; omega), h6]
    rfl
  have hd1 : (JuliaLean.base.int.band
      (JuliaLean.base.int.widenTo .i64
        (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 1)))
      (JuliaLean.base.int.lit .i64 3)).val = (flags.val / 2) % 4 := by
    rw [band_widen_u8_three_val, hshr1]
  have hd3 : (JuliaLean.base.int.band
      (JuliaLean.base.int.widenTo .i64
        (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 3)))
      (JuliaLean.base.int.lit .i64 3)).val = (flags.val / 8) % 4 := by
    rw [band_widen_u8_three_val, hshr3]
  have hd6 : (JuliaLean.base.int.band
      (JuliaLean.base.int.widenTo .i64
        (JuliaLean.base.int.shr_Int flags (JuliaLean.base.int.lit .i64 6)))
      (JuliaLean.base.int.lit .i64 3)).val = (flags.val / 64) % 4 := by
    rw [band_widen_u8_three_val, hshr6]
  rw [hd1, hd3, hd6]
  refine ⟨decide_eq_true_iff, rfl, rfl, decide_eq_true_iff, rfl, int_byte_digits_sum flags.val hflags⟩

private theorem flagByteDigits_unique {flags : JInt .u8}
    {f f' : JuliaLean.base.loading.Models2Group4.FlagByteFields}
    (hdig : Models2Group4.FlagByteDigits flags f)
    (hdig' : Models2Group4.FlagByteDigits flags f') : f' = f := by
  cases f'; cases f
  unfold Models2Group4.FlagByteDigits at hdig hdig'
  dsimp only at hdig hdig'
  rcases hdig with ⟨hu, hd, hc, hi, ho, _⟩
  rcases hdig' with ⟨hu', hd', hc', hi', ho', _⟩
  have h1 := Bool.eq_iff_iff.mpr (hu'.trans hu.symm)
  have h2 := Subtype.ext (hd'.trans hd.symm)
  have h3 := Subtype.ext (hc'.trans hc.symm)
  have h4 := Bool.eq_iff_iff.mpr (hi'.trans hi.symm)
  have h5 := Subtype.ext (ho'.trans ho.symm)
  subst h1 h2 h3 h4 h5; rfl

private theorem flagNativeLiftInvariant_proven :
    Models2Group4.FlagNativeLiftInvariant := by
  intro E W A action world
  refine ⟨?_, ?_, ?_⟩
  · intro value h; subst h; rfl
  · intro message h; subst h; rfl
  · intro error h hne
    subst h
    cases error with
    | argumentError msg => exact False.elim (hne msg rfl)
    | _ => rfl

private theorem cacheFlagsFromUInt8_diverges_none {E W C Converted Inner : Type}
    (ops : JuliaLean.base.loading.Models2Group4.FlagByteOps
      (Models2Group4.ObservationM (Sum JlError E) W) C Converted Inner)
    (flags : JInt .u8) (coverage : C) (world : W)
    (hdiv : Models2Group4.FlagByteDiverges ops flags coverage world) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E) ops flags coverage) world = none := by
  unfold JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8
  rw [decodeCacheFlagByte_eq]
  dsimp only [JuliaLean.base.loading.Models2Group4.liftFlagNative]
  rw [observe_bind, observe_pure]
  dsimp only
  rw [observe_bind]
  rcases hdiv with hto | ⟨f', converted, w1, hdig', hto, hbranch⟩
  · rw [hto]
  · rw [hto]
    have hf := flagByteDigits_unique (expectedFlagByteFields_digits flags) hdig'
    subst hf
    dsimp only
    unfold JuliaLean.base.loading.Models2Group4.selectedFlagSix
      JuliaLean.base.loading.Models2Group4.cacheFlagsSix
    rcases hbranch with ⟨hsel, h7⟩ | ⟨hsel, hcust⟩
    · rw [hsel]; exact h7
    · rw [hsel]; exact hcust

private theorem cacheFlagsFromUInt8_produces_ok {E W C Converted Inner : Type}
    (ops : JuliaLean.base.loading.Models2Group4.FlagByteOps
      (Models2Group4.ObservationM (Sum JlError E) W) C Converted Inner)
    (flags : JInt .u8) (coverage : C) (world : W) (inner : Inner) (after : W)
    (hprod : Models2Group4.FlagByteProduces ops flags coverage world inner after) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E) ops flags coverage) world =
      some (.ok inner, after) := by
  unfold JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8
  rw [decodeCacheFlagByte_eq]
  dsimp only [JuliaLean.base.loading.Models2Group4.liftFlagNative]
  rw [observe_bind, observe_pure]
  dsimp only
  rw [observe_bind]
  rcases hprod with ⟨f', converted, w1, hdig', hto, hbranch⟩
  rw [hto]
  have hf := flagByteDigits_unique (expectedFlagByteFields_digits flags) hdig'
  subst hf
  dsimp only
  unfold JuliaLean.base.loading.Models2Group4.selectedFlagSix
    JuliaLean.base.loading.Models2Group4.cacheFlagsSix
  rcases hbranch with ⟨hsel, h7⟩ | ⟨hsel, hcust⟩
  · rw [hsel]; exact h7
  · rw [hsel]; exact hcust

private theorem cacheFlagsFromUInt8_spec {E W C Converted Inner Result : Type}
    (ops : JuliaLean.base.loading.Models2Group4.FlagByteOps
      (Models2Group4.ObservationM (Sum JlError E) W) C Converted Inner)
    (flags : JInt .u8) (coverage : C) (world : W)
    (evs : List (Models2Group4.FlagByteEvent E W C Converted Inner Result)) :
    let traced := Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E)
        (Models2Group4.traceFlagByte (Result := Result) ops) flags coverage) (world, evs)
    let plain := Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E) ops flags coverage) world
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ result after events, traced = some (result, (after, events)) →
      ∃ suffix, events = evs ++ suffix ∧
        Models2Group4.FlagByteTrace ops.six.selection flags coverage world result after suffix) ∧
    (plain = none ↔ Models2Group4.FlagByteDiverges ops flags coverage world) ∧
    (∀ inner after, plain = some (.ok inner, after) ↔
      Models2Group4.FlagByteProduces ops flags coverage world inner after) := by
  dsimp only
  have hmpr_div := cacheFlagsFromUInt8_diverges_none ops flags coverage world
  have hmpr_prod := cacheFlagsFromUInt8_produces_ok ops flags coverage world
  suffices hmain :
      (Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E)
          (Models2Group4.traceFlagByte (Result := Result) ops) flags coverage) (world, evs)).map
        (fun observation => (observation.1, observation.2.1)) =
      Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E) ops flags coverage) world ∧
      (∀ result after events,
        Models2Group4.observe
          (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E)
            (Models2Group4.traceFlagByte (Result := Result) ops) flags coverage) (world, evs) =
          some (result, (after, events)) →
        ∃ suffix, events = evs ++ suffix ∧
          Models2Group4.FlagByteTrace ops.six.selection flags coverage world result after suffix) ∧
      (Models2Group4.observe
        (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E) ops flags coverage) world = none →
        Models2Group4.FlagByteDiverges ops flags coverage world) ∧
      (∀ inner after,
        Models2Group4.observe
          (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E) ops flags coverage) world =
          some (.ok inner, after) →
        Models2Group4.FlagByteProduces ops flags coverage world inner after) by
    exact And.intro hmain.1 (And.intro hmain.2.1
      (And.intro (Iff.intro hmain.2.2.1 hmpr_div)
        (fun inner after => Iff.intro (hmain.2.2.2 inner after) (hmpr_prod inner after))))
  unfold JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8
    Models2Group4.traceFlagByte Models2Group4.FlagByteTrace
    Models2Group4.FlagByteDiverges Models2Group4.FlagByteProduces
  rw [decodeCacheFlagByte_eq]
  dsimp only [JuliaLean.base.loading.Models2Group4.liftFlagNative]
  rw [observe_bind, observe_pure, observe_bind, observe_pure]
  dsimp only
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  have hdig := expectedFlagByteFields_digits flags
  cases hto : Models2Group4.observe (ops.toInt coverage) world with
  | none =>
      exact ⟨rfl, (fun _ _ _ h => nomatch h), fun _ => Or.inl rfl, (fun _ _ h => nomatch h)⟩
  | some p1 =>
      rcases p1 with ⟨res1, w1⟩
      cases res1 with
      | error err =>
          refine ⟨rfl, ?_, (fun h => nomatch h), (fun _ _ h => nomatch h)⟩
          intro result after events h
          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
          subst hres hfw
          exact ⟨[.convertCoverage coverage world (.error err) w1], hev.symm,
            Or.inl ⟨err, rfl, rfl⟩⟩
      | ok converted =>
          dsimp only
          unfold JuliaLean.base.loading.Models2Group4.selectedFlagSix
            Models2Group4.traceFlagSixDispatch Models2Group4.FlagByteSixTrace
            JuliaLean.base.loading.Models2Group4.cacheFlagsSix
          let f := expectedFlagByteFields flags
          cases hsel : ops.six.selection f converted with
          | base =>
              dsimp only
              rw [observe_recordPackageStep]
              cases h7 : Models2Group4.observe
                  (ops.six.baseOps.constructSeven f.usePkgimages f.debugLevel f.checkBounds
                    f.inlineValue f.optLevel converted none) w1 with
              | none =>
                  exact ⟨rfl, (fun _ _ _ h => nomatch h),
                    fun _ => Or.inr ⟨f, converted, w1, hdig, rfl, Or.inl ⟨hsel, h7⟩⟩,
                    (fun _ _ h => nomatch h)⟩
              | some p2 =>
                  rcases p2 with ⟨res2, w2⟩
                  refine ⟨rfl, ?_, (fun h => nomatch h), ?_⟩
                  · intro result after events h
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    subst hres hfw
                    refine ⟨[.convertCoverage coverage world (.ok converted) w1,
                      .seven f converted none w1 res2 w2], ?_,
                      Or.inr ⟨f, converted, w1, [.seven f converted none w1 res2 w2],
                        hdig, rfl, Or.inl ⟨hsel, rfl⟩⟩⟩
                    rw [← hev]; simp only [List.append_assoc]; rfl
                  · intro inner after h
                    cases h
                    exact ⟨f, converted, w1, hdig, rfl, Or.inl ⟨hsel, h7⟩⟩
          | custom =>
              dsimp only
              rw [observe_recordPackageStep]
              cases hcust : Models2Group4.observe
                  (ops.six.custom f.usePkgimages f.debugLevel f.checkBounds
                    f.inlineValue f.optLevel converted) w1 with
              | none =>
                  exact ⟨rfl, (fun _ _ _ h => nomatch h),
                    fun _ => Or.inr ⟨f, converted, w1, hdig, rfl, Or.inr ⟨hsel, hcust⟩⟩,
                    (fun _ _ h => nomatch h)⟩
              | some p2 =>
                  rcases p2 with ⟨res2, w2⟩
                  refine ⟨rfl, ?_, (fun h => nomatch h), ?_⟩
                  · intro result after events h
                    injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                    subst hres hfw
                    refine ⟨[.convertCoverage coverage world (.ok converted) w1,
                      .customSix f converted w1 res2 w2], ?_,
                      Or.inr ⟨f, converted, w1, [.customSix f converted w1 res2 w2],
                        hdig, rfl, Or.inr ⟨hsel, rfl⟩⟩⟩
                    rw [← hev]; simp only [List.append_assoc]; rfl
                  · intro inner after h
                    cases h
                    exact ⟨f, converted, w1, hdig, rfl, Or.inr ⟨hsel, hcust⟩⟩

theorem cacheFlagsUInt8Correct_proven :
    Models2Group4.CacheFlagsUInt8Correct := by
  refine ⟨flagNativeLiftInvariant_proven,
    fun flags => ⟨expectedFlagByteFields flags, decodeCacheFlagByte_eq flags, expectedFlagByteFields_digits flags⟩,
    ?_, ?_⟩
  · intro E W C Converted Result ops flags coverage world
    have hspec := cacheFlagsFromUInt8_spec (Result := Unit) ops flags coverage world []
    refine And.intro hspec.1 (And.intro ?_ hspec.2.2.1)
    intro result after events h
    obtain ⟨suffix, hsuf, htr⟩ := hspec.2.1 result after events h
    rw [List.nil_append] at hsuf
    subst hsuf
    exact htr
  · intro E W flags world
    unfold JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Default
    rw [decodeCacheFlagByte_eq, convert_i64_self]
    dsimp only [JuliaLean.base.loading.Models2Group4.liftFlagNative,
      Bind.bind, Pure.pure]
    let f := expectedFlagByteFields flags
    refine ⟨JuliaLean.base.loading.CacheFlags_fields f.usePkgimages f.debugLevel f.checkBounds
      f.inlineValue f.optLevel (JuliaLean.base.int.lit .i64 0),
      rfl, expectedFlagByteFields_digits flags, wrap_i64_zero, rfl⟩

-- 11. loading-cache-flags-uint8-path
private theorem cacheFlagsFromUInt8Path_diverges_none {E W C Converted Inner Result : Type}
    (ops : JuliaLean.base.loading.Models2Group4.FlagPathOps
      (Models2Group4.ObservationM (Sum JlError E) W) C Converted Inner Result)
    (flags : JInt .u8) (coverage : C) (path : Option JuliaLean.Strings.JStr) (world : W)
    (hdiv : Models2Group4.FlagPathDiverges ops flags coverage path world) :
    Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Path (E := E) ops flags coverage path) world = none := by
  unfold JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Path
    JuliaLean.base.loading.Models2Group4.selectedFlagByte
  rw [observe_bind]
  rcases hdiv with ⟨hsel, h1⟩ | ⟨hsel, h1⟩ | ⟨inner, w1, hprod, hkw⟩
  · rw [hsel, cacheFlagsFromUInt8_diverges_none ops.inner.baseOps flags coverage world h1]
  · rw [hsel, h1]
  · rcases hprod with ⟨hsel, hp⟩ | ⟨hsel, hp⟩
    · rw [hsel, cacheFlagsFromUInt8_produces_ok ops.inner.baseOps flags coverage world inner w1 hp]
      exact hkw
    · rw [hsel, hp]; exact hkw

theorem cacheFlagsUInt8PathCorrect_proven :
    Models2Group4.CacheFlagsUInt8PathCorrect := by
  intro E W C Converted Inner Result ops flags coverage path world
  dsimp only
  have hmpr := cacheFlagsFromUInt8Path_diverges_none ops flags coverage path world
  suffices hmain :
      (Models2Group4.observe (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Path (E := E)
        (Models2Group4.traceFlagPath ops) flags coverage path) (world, [])).map
        (fun observation => (observation.1, observation.2.1)) =
      Models2Group4.observe (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Path (E := E)
        ops flags coverage path) world ∧
      (∀ result after events,
        Models2Group4.observe (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Path (E := E)
          (Models2Group4.traceFlagPath ops) flags coverage path) (world, []) =
          some (result, (after, events)) →
        Models2Group4.FlagPathTrace (ops.inner.selection flags coverage) ops.inner.baseOps.six.selection
          flags coverage path world result after events) ∧
      (Models2Group4.observe (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Path (E := E)
        ops flags coverage path) world = none →
        Models2Group4.FlagPathDiverges ops flags coverage path world) by
    exact And.intro hmain.1 (And.intro hmain.2.1 (Iff.intro hmain.2.2 hmpr))
  unfold JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8Path
    JuliaLean.base.loading.Models2Group4.selectedFlagByte
    Models2Group4.traceFlagPath Models2Group4.traceFlagByteDispatch
    Models2Group4.FlagPathTrace Models2Group4.FlagPathDiverges
  rw [observe_bind, observe_bind]
  cases hsel : ops.inner.selection flags coverage with
  | base =>
      dsimp only
      have hspec := cacheFlagsFromUInt8_spec (Result := Result) ops.inner.baseOps flags coverage world []
      cases htraced : Models2Group4.observe
          (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E)
            (Models2Group4.traceFlagByte (Result := Result) ops.inner.baseOps) flags coverage) (world, []) with
      | none =>
          have hplain : Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E)
                ops.inner.baseOps flags coverage) world = none := by
            rw [← hspec.1, htraced]; rfl
          rw [hplain]
          dsimp only
          exact ⟨rfl, (fun _ _ _ h => nomatch h), fun _ => Or.inl ⟨rfl, hspec.2.2.1.mp hplain⟩⟩
      | some p1 =>
          rcases p1 with ⟨innerOutcome, w1, pref⟩
          have hplain : Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.cacheFlagsFromUInt8 (E := E)
                ops.inner.baseOps flags coverage) world = some (innerOutcome, w1) := by
            rw [← hspec.1, htraced]; rfl
          rw [hplain]
          obtain ⟨suf0, hsuf0, hbtr⟩ := hspec.2.1 innerOutcome w1 pref htraced
          rw [List.nil_append] at hsuf0
          subst hsuf0
          cases innerOutcome with
          | error err =>
              refine ⟨rfl, ?_, (fun h => nomatch h)⟩
              intro result after events h
              injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
              subst hres hfw
              exact ⟨.error err, w1, pref, [], (by rw [List.append_nil]; exact hev.symm),
                Or.inl ⟨rfl, hbtr⟩, rfl, rfl, rfl⟩
          | ok inner =>
              dsimp only
              rw [observe_recordPackageStep]
              have hprod : Models2Group4.FlagByteProduces ops.inner.baseOps flags coverage world inner w1 :=
                (hspec.2.2.2 inner w1).mp hplain
              cases hkw : Models2Group4.observe (ops.keyword inner path) w1 with
              | none =>
                  dsimp only
                  exact ⟨rfl, (fun _ _ _ h => nomatch h),
                    fun _ => Or.inr (Or.inr ⟨inner, w1, Or.inl ⟨rfl, hprod⟩, hkw⟩)⟩
              | some p2 =>
                  rcases p2 with ⟨res2, w2⟩
                  refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                  intro result after events h
                  injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                  subst hres hfw
                  exact ⟨.ok inner, w1, pref, [.keyword inner path w1 res2 w2], hev.symm,
                    Or.inl ⟨rfl, hbtr⟩, rfl⟩
  | custom =>
      dsimp only
      rw [observe_recordPackageStep]
      cases hcust : Models2Group4.observe (ops.inner.custom flags coverage) world with
      | none =>
          dsimp only
          exact ⟨rfl, (fun _ _ _ h => nomatch h), fun _ => Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      | some p1 =>
          rcases p1 with ⟨innerOutcome, w1⟩
          cases innerOutcome with
          | error err =>
              refine ⟨rfl, ?_, (fun h => nomatch h)⟩
              intro result after events h
              injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
              subst hres hfw
              exact ⟨.error err, w1, [.customByte flags coverage world (.error err) w1], [],
                (by rw [List.append_nil]; exact hev.symm),
                Or.inr ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
          | ok inner =>
              dsimp only
              rw [observe_recordPackageStep]
              cases hkw : Models2Group4.observe (ops.keyword inner path) w1 with
              | none =>
                  dsimp only
                  exact ⟨rfl, (fun _ _ _ h => nomatch h),
                    fun _ => Or.inr (Or.inr ⟨inner, w1, Or.inr ⟨rfl, rfl⟩, hkw⟩)⟩
              | some p2 =>
                  rcases p2 with ⟨res2, w2⟩
                  refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                  intro result after events h
                  injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                  subst hres hfw
                  exact ⟨.ok inner, w1, [.customByte flags coverage world (.ok inner) w1],
                    [.keyword inner path w1 res2 w2], hev.symm,
                    Or.inr ⟨rfl, rfl⟩, rfl⟩

-- 12. loading-check-for-hint
private theorem hintParent_diverges_none {W L : Type}
    (ops : JuliaLean.base.loading.Models2Group4.HintOps W L)
    (into selector : JuliaLean.base.loading.Models2Group4.GenericValue L)
    (w : W)
    (hdiv : Models2Group4.observe (ops.parentmodule into) w = none ∨
      ∃ firstParent w1,
        Models2Group4.observe (ops.parentmodule into) w = some (.ok firstParent, w1) ∧
        (Models2Group4.observe
            (JuliaLean.base.loading.Models2Group4.liftCoreAction
              (ops.defined.isdefined firstParent selector)) w1 = none ∨
          ∃ w2,
            Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.defined.isdefined firstParent selector)) w1 = some (.ok true, w2) ∧
            (Models2Group4.observe (ops.parentmodule into) w2 = none ∨
              ∃ secondParent w3,
                Models2Group4.observe (ops.parentmodule into) w2 = some (.ok secondParent, w3) ∧
                Models2Group4.observe
                  (JuliaLean.base.loading.Models2Group4.liftCoreAction
                    (ops.core.getfield secondParent selector)) w3 = none))) :
    Models2Group4.observe (do
      let firstParent ← ops.parentmodule into
      if ← JuliaLean.base.loading.Models2Group4.liftCoreAction
          (ops.defined.isdefined firstParent selector) then
        let secondParent ← ops.parentmodule into
        let field ← JuliaLean.base.loading.Models2Group4.liftCoreAction
          (ops.core.getfield secondParent selector)
        if ops.core.isa field (JuliaLean.base.boot.coreV ops.core "Module") then
          return JuliaLean.base.loading.Models2Group4.hintTuple
            ops.core true JuliaLean.base.loading.Models2Group4.hintParentDots
        else
          return JuliaLean.base.loading.Models2Group4.hintTuple
            ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty
      else
        return JuliaLean.base.loading.Models2Group4.hintTuple
          ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty) w = none := by
  rw [observe_bind]
  rcases hdiv with hp1 | ⟨firstParent, w1, hp1, h2⟩
  · rw [hp1]
  · rw [hp1]
    dsimp only
    rw [observe_bind]
    rcases h2 with hdef | ⟨w2, hdef, h3⟩
    · rw [hdef]
    · rw [hdef]
      simp only [↓reduceIte]
      rw [observe_bind]
      rcases h3 with hp2 | ⟨secondParent, w3, hp2, hfld⟩
      · rw [hp2]
      · rw [hp2]
        dsimp only
        rw [observe_bind, hfld]

private theorem hintParent_spec {W L : Type}
    (ops : JuliaLean.base.loading.Models2Group4.HintOps W L)
    (otherCore : JuliaLean.base.boot.CoreOps (W × List (Models2Group4.HintEvent W L)) L)
    (into selector : JuliaLean.base.loading.Models2Group4.GenericValue L)
    (w : W) (evs : List (Models2Group4.HintEvent W L)) :
    let traced := Models2Group4.observe (do
      let firstParent ← (Models2Group4.traceHint ops otherCore).parentmodule into
      if ← JuliaLean.base.loading.Models2Group4.liftCoreAction
          ((Models2Group4.traceHint ops otherCore).defined.isdefined firstParent selector) then
        let secondParent ← (Models2Group4.traceHint ops otherCore).parentmodule into
        let field ← JuliaLean.base.loading.Models2Group4.liftCoreAction
          ((Models2Group4.traceHint ops otherCore).core.getfield secondParent selector)
        if (Models2Group4.traceHint ops otherCore).core.isa field
            (JuliaLean.base.boot.coreV (Models2Group4.traceHint ops otherCore).core "Module") then
          return JuliaLean.base.loading.Models2Group4.hintTuple
            (Models2Group4.traceHint ops otherCore).core true JuliaLean.base.loading.Models2Group4.hintParentDots
        else
          return JuliaLean.base.loading.Models2Group4.hintTuple
            (Models2Group4.traceHint ops otherCore).core false JuliaLean.base.loading.Models2Group4.hintEmpty
      else
        return JuliaLean.base.loading.Models2Group4.hintTuple
          (Models2Group4.traceHint ops otherCore).core false JuliaLean.base.loading.Models2Group4.hintEmpty) (w, evs)
    let plain := Models2Group4.observe (do
      let firstParent ← ops.parentmodule into
      if ← JuliaLean.base.loading.Models2Group4.liftCoreAction
          (ops.defined.isdefined firstParent selector) then
        let secondParent ← ops.parentmodule into
        let field ← JuliaLean.base.loading.Models2Group4.liftCoreAction
          (ops.core.getfield secondParent selector)
        if ops.core.isa field (JuliaLean.base.boot.coreV ops.core "Module") then
          return JuliaLean.base.loading.Models2Group4.hintTuple
            ops.core true JuliaLean.base.loading.Models2Group4.hintParentDots
        else
          return JuliaLean.base.loading.Models2Group4.hintTuple
            ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty
      else
        return JuliaLean.base.loading.Models2Group4.hintTuple
          ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty) w
    traced.map (fun observation => (observation.1, observation.2.1)) = plain ∧
    (∀ outcome after events, traced = some (outcome, (after, events)) →
      ∃ suffix, events = evs ++ suffix ∧
        Models2Group4.HintParentTrace ops.core into selector w outcome after suffix) ∧
    (plain = none ↔
      Models2Group4.observe (ops.parentmodule into) w = none ∨
      ∃ firstParent w1,
        Models2Group4.observe (ops.parentmodule into) w = some (.ok firstParent, w1) ∧
        (Models2Group4.observe
            (JuliaLean.base.loading.Models2Group4.liftCoreAction
              (ops.defined.isdefined firstParent selector)) w1 = none ∨
          ∃ w2,
            Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.defined.isdefined firstParent selector)) w1 = some (.ok true, w2) ∧
            (Models2Group4.observe (ops.parentmodule into) w2 = none ∨
              ∃ secondParent w3,
                Models2Group4.observe (ops.parentmodule into) w2 = some (.ok secondParent, w3) ∧
                Models2Group4.observe
                  (JuliaLean.base.loading.Models2Group4.liftCoreAction
                    (ops.core.getfield secondParent selector)) w3 = none))) := by
  dsimp only
  suffices hmain :
      (Models2Group4.observe (do
        let firstParent ← (Models2Group4.traceHint ops otherCore).parentmodule into
        if ← JuliaLean.base.loading.Models2Group4.liftCoreAction
            ((Models2Group4.traceHint ops otherCore).defined.isdefined firstParent selector) then
          let secondParent ← (Models2Group4.traceHint ops otherCore).parentmodule into
          let field ← JuliaLean.base.loading.Models2Group4.liftCoreAction
            ((Models2Group4.traceHint ops otherCore).core.getfield secondParent selector)
          if (Models2Group4.traceHint ops otherCore).core.isa field
              (JuliaLean.base.boot.coreV (Models2Group4.traceHint ops otherCore).core "Module") then
            return JuliaLean.base.loading.Models2Group4.hintTuple
              (Models2Group4.traceHint ops otherCore).core true JuliaLean.base.loading.Models2Group4.hintParentDots
          else
            return JuliaLean.base.loading.Models2Group4.hintTuple
              (Models2Group4.traceHint ops otherCore).core false JuliaLean.base.loading.Models2Group4.hintEmpty
        else
          return JuliaLean.base.loading.Models2Group4.hintTuple
            (Models2Group4.traceHint ops otherCore).core false JuliaLean.base.loading.Models2Group4.hintEmpty) (w, evs)).map
        (fun observation => (observation.1, observation.2.1)) =
      Models2Group4.observe (do
        let firstParent ← ops.parentmodule into
        if ← JuliaLean.base.loading.Models2Group4.liftCoreAction
            (ops.defined.isdefined firstParent selector) then
          let secondParent ← ops.parentmodule into
          let field ← JuliaLean.base.loading.Models2Group4.liftCoreAction
            (ops.core.getfield secondParent selector)
          if ops.core.isa field (JuliaLean.base.boot.coreV ops.core "Module") then
            return JuliaLean.base.loading.Models2Group4.hintTuple
              ops.core true JuliaLean.base.loading.Models2Group4.hintParentDots
          else
            return JuliaLean.base.loading.Models2Group4.hintTuple
              ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty
        else
          return JuliaLean.base.loading.Models2Group4.hintTuple
            ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty) w ∧
      (∀ outcome after events,
        Models2Group4.observe (do
          let firstParent ← (Models2Group4.traceHint ops otherCore).parentmodule into
          if ← JuliaLean.base.loading.Models2Group4.liftCoreAction
              ((Models2Group4.traceHint ops otherCore).defined.isdefined firstParent selector) then
            let secondParent ← (Models2Group4.traceHint ops otherCore).parentmodule into
            let field ← JuliaLean.base.loading.Models2Group4.liftCoreAction
              ((Models2Group4.traceHint ops otherCore).core.getfield secondParent selector)
            if (Models2Group4.traceHint ops otherCore).core.isa field
                (JuliaLean.base.boot.coreV (Models2Group4.traceHint ops otherCore).core "Module") then
              return JuliaLean.base.loading.Models2Group4.hintTuple
                (Models2Group4.traceHint ops otherCore).core true JuliaLean.base.loading.Models2Group4.hintParentDots
            else
              return JuliaLean.base.loading.Models2Group4.hintTuple
                (Models2Group4.traceHint ops otherCore).core false JuliaLean.base.loading.Models2Group4.hintEmpty
          else
            return JuliaLean.base.loading.Models2Group4.hintTuple
              (Models2Group4.traceHint ops otherCore).core false JuliaLean.base.loading.Models2Group4.hintEmpty) (w, evs) =
          some (outcome, (after, events)) →
        ∃ suffix, events = evs ++ suffix ∧
          Models2Group4.HintParentTrace ops.core into selector w outcome after suffix) ∧
      (Models2Group4.observe (do
        let firstParent ← ops.parentmodule into
        if ← JuliaLean.base.loading.Models2Group4.liftCoreAction
            (ops.defined.isdefined firstParent selector) then
          let secondParent ← ops.parentmodule into
          let field ← JuliaLean.base.loading.Models2Group4.liftCoreAction
            (ops.core.getfield secondParent selector)
          if ops.core.isa field (JuliaLean.base.boot.coreV ops.core "Module") then
            return JuliaLean.base.loading.Models2Group4.hintTuple
              ops.core true JuliaLean.base.loading.Models2Group4.hintParentDots
          else
            return JuliaLean.base.loading.Models2Group4.hintTuple
              ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty
        else
          return JuliaLean.base.loading.Models2Group4.hintTuple
            ops.core false JuliaLean.base.loading.Models2Group4.hintEmpty) w = none →
        Models2Group4.observe (ops.parentmodule into) w = none ∨
        ∃ firstParent w1,
          Models2Group4.observe (ops.parentmodule into) w = some (.ok firstParent, w1) ∧
          (Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.defined.isdefined firstParent selector)) w1 = none ∨
            ∃ w2,
              Models2Group4.observe
                (JuliaLean.base.loading.Models2Group4.liftCoreAction
                  (ops.defined.isdefined firstParent selector)) w1 = some (.ok true, w2) ∧
              (Models2Group4.observe (ops.parentmodule into) w2 = none ∨
                ∃ secondParent w3,
                  Models2Group4.observe (ops.parentmodule into) w2 = some (.ok secondParent, w3) ∧
                  Models2Group4.observe
                    (JuliaLean.base.loading.Models2Group4.liftCoreAction
                      (ops.core.getfield secondParent selector)) w3 = none))) by
    exact And.intro hmain.1 (And.intro hmain.2.1 (Iff.intro hmain.2.2 (hintParent_diverges_none ops into selector w)))
  dsimp only [Models2Group4.traceHint, JuliaLean.base.boot.coreV,
    JuliaLean.base.loading.Models2Group4.hintTuple, JuliaLean.base.boot.tupleV,
    JuliaLean.base.boot.boolV, JuliaLean.base.boot.strV]
  rw [observe_bind, observe_bind, observe_recordPackageStep]
  cases hp1 : Models2Group4.observe (ops.parentmodule into) w with
  | none =>
      exact ⟨rfl, (fun _ _ _ h => nomatch h), fun _ => Or.inl rfl⟩
  | some p1 =>
      rcases p1 with ⟨res1, w1⟩
      cases res1 with
      | error err =>
          refine ⟨rfl, ?_, (fun h => nomatch h)⟩
          intro outcome after events h
          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
          subst hres hfw
          exact ⟨[.parent into w (.error err) w1], hev.symm, .firstError w w1 err⟩
      | ok firstParent =>
          dsimp only
          rw [observe_bind, observe_bind, observe_recordHintCore]
          cases hdef : Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.defined.isdefined firstParent selector)) w1 with
          | none =>
              dsimp only
              exact ⟨rfl, (fun _ _ _ h => nomatch h),
                fun _ => Or.inr ⟨firstParent, w1, rfl, Or.inl hdef⟩⟩
          | some p2 =>
              rcases p2 with ⟨res2, w2⟩
              cases res2 with
              | error err =>
                  refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                  intro outcome after events h
                  injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                  subst hres hfw
                  refine ⟨[.parent into w (.ok firstParent) w1,
                    .defined firstParent selector w1 (.error err) w2], ?_,
                    .definedError w w1 w2 firstParent err⟩
                  rw [← hev]; simp only [List.append_assoc]; rfl
              | ok b =>
                  cases b with
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte, observe_pure]
                      refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                      intro outcome after events h
                      injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                      subst hres hfw
                      refine ⟨[.parent into w (.ok firstParent) w1,
                        .defined firstParent selector w1 (.ok false) w2], ?_,
                        .undefined w w1 w2 firstParent _ rfl⟩
                      rw [← hev]; simp only [List.append_assoc]; rfl
                  | true =>
                      simp only [↓reduceIte]
                      rw [observe_bind, observe_bind, observe_recordPackageStep]
                      cases hp2 : Models2Group4.observe (ops.parentmodule into) w2 with
                      | none =>
                          dsimp only
                          exact ⟨rfl, (fun _ _ _ h => nomatch h),
                            fun _ => Or.inr ⟨firstParent, w1, rfl, Or.inr ⟨w2, hdef, Or.inl hp2⟩⟩⟩
                      | some p3 =>
                          rcases p3 with ⟨res3, w3⟩
                          cases res3 with
                          | error err =>
                              refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                              intro outcome after events h
                              injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                              subst hres hfw
                              refine ⟨[.parent into w (.ok firstParent) w1,
                                .defined firstParent selector w1 (.ok true) w2,
                                .parent into w2 (.error err) w3], ?_,
                                .secondError w w1 w2 w3 firstParent err⟩
                              rw [← hev]; simp only [List.append_assoc]; rfl
                          | ok secondParent =>
                              dsimp only
                              rw [observe_bind, observe_bind, observe_recordHintCore]
                              cases hfld : Models2Group4.observe
                                  (JuliaLean.base.loading.Models2Group4.liftCoreAction
                                    (ops.core.getfield secondParent selector)) w3 with
                              | none =>
                                  dsimp only
                                  exact ⟨rfl, (fun _ _ _ h => nomatch h),
                                    fun _ => Or.inr ⟨firstParent, w1, rfl,
                                      Or.inr ⟨w2, hdef, Or.inr ⟨secondParent, w3, hp2, hfld⟩⟩⟩⟩
                              | some p4 =>
                                  rcases p4 with ⟨res4, w4⟩
                                  cases res4 with
                                  | error err =>
                                      refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                      intro outcome after events h
                                      injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                      subst hres hfw
                                      refine ⟨[.parent into w (.ok firstParent) w1,
                                        .defined firstParent selector w1 (.ok true) w2,
                                        .parent into w2 (.ok secondParent) w3,
                                        .field secondParent selector w3 (.error err) w4], ?_,
                                        .fieldError w w1 w2 w3 w4 firstParent secondParent err⟩
                                      rw [← hev]; simp only [List.append_assoc]; rfl
                                  | ok field =>
                                      dsimp only
                                      by_cases hisa : ops.core.isa field (.leaf (ops.core.core "Module")) = true
                                      · simp only [hisa, ↓reduceIte, observe_pure]
                                        refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                        intro outcome after events h
                                        injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                        subst hres hfw
                                        refine ⟨[.parent into w (.ok firstParent) w1,
                                          .defined firstParent selector w1 (.ok true) w2,
                                          .parent into w2 (.ok secondParent) w3,
                                          .field secondParent selector w3 (.ok field) w4], ?_,
                                          .module w w1 w2 w3 w4 firstParent secondParent field _ hisa rfl⟩
                                        rw [← hev]; simp only [List.append_assoc]; rfl
                                      · have hisaf : ops.core.isa field (.leaf (ops.core.core "Module")) = false :=
                                          Bool.eq_false_iff.mpr hisa
                                        simp only [hisaf, Bool.false_eq_true, ↓reduceIte, observe_pure]
                                        refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                                        intro outcome after events h
                                        injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                                        subst hres hfw
                                        refine ⟨[.parent into w (.ok firstParent) w1,
                                          .defined firstParent selector w1 (.ok true) w2,
                                          .parent into w2 (.ok secondParent) w3,
                                          .field secondParent selector w3 (.ok field) w4], ?_,
                                          .nonModule w w1 w2 w3 w4 firstParent secondParent field _ hisaf rfl⟩
                                        rw [← hev]; simp only [List.append_assoc]; rfl

private theorem checkForHint_diverges_none {W L : Type}
    (ops : JuliaLean.base.loading.Models2Group4.HintOps W L)
    (into selector : JuliaLean.base.loading.Models2Group4.GenericValue L)
    (world : W)
    (hdiv : Models2Group4.HintDiverges ops into selector world) :
    Models2Group4.observe (JuliaLean.base.loading.Models2Group4.checkForHint ops into selector) world = none := by
  unfold JuliaLean.base.loading.Models2Group4.checkForHint
  rcases hdiv with ⟨pt, bef, hreach, hnone⟩
  cases hreach with
  | start =>
      dsimp only at hnone
      rw [observe_bind, hnone]
  | ownField _ hdef0 =>
      dsimp only at hnone
      rw [observe_bind, hdef0]
      simp only [↓reduceIte]
      rw [observe_bind, hnone]
  | firstAfterUndefined _ hdef0 =>
      dsimp only at hnone
      rw [observe_bind, hdef0]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hintParent_diverges_none ops into selector _ (Or.inl hnone)
  | firstAfterNonModule _ _ field h1 hfld0 hisa0 =>
      cases h1 with
      | ownField _ hdef0 =>
          dsimp only at hnone
          rw [observe_bind, hdef0]
          simp only [↓reduceIte]
          rw [observe_bind, hfld0]
          dsimp only
          rw [hisa0]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hintParent_diverges_none ops into selector _ (Or.inl hnone)
  | parentDefined _ _ fp h1 hp1 =>
      dsimp only at hnone
      have hpdiv := hintParent_diverges_none ops into selector _ (Or.inr ⟨fp, _, hp1, Or.inl hnone⟩)
      cases h1 with
      | firstAfterUndefined _ hdef0 =>
          rw [observe_bind, hdef0]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hpdiv
      | firstAfterNonModule _ _ field h0 hfld0 hisa0 =>
          cases h0 with
          | ownField _ hdef0 =>
              rw [observe_bind, hdef0]
              simp only [↓reduceIte]
              rw [observe_bind, hfld0]
              dsimp only
              rw [hisa0]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact hpdiv
  | secondParent _ _ fp h2 hdef1 =>
      cases h2 with
      | parentDefined _ _ _ h1 hp1 =>
          dsimp only at hnone
          have hpdiv := hintParent_diverges_none ops into selector _
            (Or.inr ⟨fp, _, hp1, Or.inr ⟨_, hdef1, Or.inl hnone⟩⟩)
          cases h1 with
          | firstAfterUndefined _ hdef0 =>
              rw [observe_bind, hdef0]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact hpdiv
          | firstAfterNonModule _ _ field h0 hfld0 hisa0 =>
              cases h0 with
              | ownField _ hdef0 =>
                  rw [observe_bind, hdef0]
                  simp only [↓reduceIte]
                  rw [observe_bind, hfld0]
                  dsimp only
                  rw [hisa0]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hpdiv
  | parentField _ _ sp h3 hp2 =>
      cases h3 with
      | secondParent _ _ fp h2 hdef1 =>
          cases h2 with
          | parentDefined _ _ _ h1 hp1 =>
              dsimp only at hnone
              have hpdiv := hintParent_diverges_none ops into selector _
                (Or.inr ⟨fp, _, hp1, Or.inr ⟨_, hdef1, Or.inr ⟨sp, _, hp2, hnone⟩⟩⟩)
              cases h1 with
              | firstAfterUndefined _ hdef0 =>
                  rw [observe_bind, hdef0]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hpdiv
              | firstAfterNonModule _ _ field h0 hfld0 hisa0 =>
                  cases h0 with
                  | ownField _ hdef0 =>
                      rw [observe_bind, hdef0]
                      simp only [↓reduceIte]
                      rw [observe_bind, hfld0]
                      dsimp only
                      rw [hisa0]
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact hpdiv

theorem checkForHintCorrect_proven :
    Models2Group4.CheckForHintCorrect := by
  refine ⟨by rw [JuliaLean.base.loading.Models2Group4.hintByteList]; decide,
    by rw [JuliaLean.base.loading.Models2Group4.hintByteList]; decide,
    by rw [JuliaLean.base.loading.Models2Group4.hintByteList]; decide, ?_⟩
  intro W L ops otherCore into selector world
  dsimp only
  suffices hmain :
      (Models2Group4.observe (JuliaLean.base.loading.Models2Group4.checkForHint
        (Models2Group4.traceHint ops otherCore) into selector) (world, [])).map
        (fun observation => (observation.1, observation.2.1)) =
      Models2Group4.observe (JuliaLean.base.loading.Models2Group4.checkForHint ops into selector) world ∧
      (∀ outcome after events,
        Models2Group4.observe (JuliaLean.base.loading.Models2Group4.checkForHint
          (Models2Group4.traceHint ops otherCore) into selector) (world, []) =
          some (outcome, (after, events)) →
        Models2Group4.HintTrace ops.core into selector world outcome after events) ∧
      (Models2Group4.observe (JuliaLean.base.loading.Models2Group4.checkForHint ops into selector) world = none →
        Models2Group4.HintDiverges ops into selector world) by
    exact And.intro hmain.1 (And.intro hmain.2.1 (Iff.intro hmain.2.2 (checkForHint_diverges_none ops into selector world)))
  unfold JuliaLean.base.loading.Models2Group4.checkForHint
    Models2Group4.HintDiverges
  have hparent_equiv : ∀ (w1 : W),
      Models2Group4.HintReachable ops into selector world .firstParent w1 →
      (Models2Group4.observe (ops.parentmodule into) w1 = none ∨
        ∃ firstParent w2,
          Models2Group4.observe (ops.parentmodule into) w1 = some (.ok firstParent, w2) ∧
          (Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.defined.isdefined firstParent selector)) w2 = none ∨
            ∃ w3,
              Models2Group4.observe
                (JuliaLean.base.loading.Models2Group4.liftCoreAction
                  (ops.defined.isdefined firstParent selector)) w2 = some (.ok true, w3) ∧
              (Models2Group4.observe (ops.parentmodule into) w3 = none ∨
                ∃ secondParent w4,
                  Models2Group4.observe (ops.parentmodule into) w3 = some (.ok secondParent, w4) ∧
                  Models2Group4.observe
                    (JuliaLean.base.loading.Models2Group4.liftCoreAction
                      (ops.core.getfield secondParent selector)) w4 = none))) →
      ∃ point before,
        Models2Group4.HintReachable ops into selector world point before ∧
        match point with
        | .ownDefined =>
            Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.defined.isdefined into selector)) before = none
        | .ownField =>
            Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.core.getfield into selector)) before = none
        | .firstParent => Models2Group4.observe (ops.parentmodule into) before = none
        | .parentDefined parent =>
            Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.defined.isdefined parent selector)) before = none
        | .secondParent => Models2Group4.observe (ops.parentmodule into) before = none
        | .parentField parent =>
            Models2Group4.observe
              (JuliaLean.base.loading.Models2Group4.liftCoreAction
                (ops.core.getfield parent selector)) before = none := by
    intro w1 hreach h
    rcases h with h1 | ⟨fp, w2, hp1, h2⟩
    · exact ⟨.firstParent, w1, hreach, h1⟩
    · rcases h2 with h2 | ⟨w3, hdef, h3⟩
      · exact ⟨.parentDefined fp, w2, .parentDefined w1 w2 fp hreach hp1, h2⟩
      · rcases h3 with h3 | ⟨sp, w4, hp2, h4⟩
        · exact ⟨.secondParent, w3,
            .secondParent w2 w3 fp (.parentDefined w1 w2 fp hreach hp1) hdef, h3⟩
        · exact ⟨.parentField sp, w4,
            .parentField w3 w4 sp (.secondParent w2 w3 fp (.parentDefined w1 w2 fp hreach hp1) hdef) hp2,
            h4⟩
  dsimp only [Models2Group4.traceHint, JuliaLean.base.boot.coreV,
    JuliaLean.base.loading.Models2Group4.hintTuple, JuliaLean.base.boot.tupleV,
    JuliaLean.base.boot.boolV, JuliaLean.base.boot.strV]
  rw [observe_bind, observe_bind, observe_recordHintCore]
  cases hdef0 : Models2Group4.observe
      (JuliaLean.base.loading.Models2Group4.liftCoreAction
        (ops.defined.isdefined into selector)) world with
  | none =>
      exact ⟨rfl, (fun _ _ _ h => nomatch h), fun _ => ⟨.ownDefined, world, .start, hdef0⟩⟩
  | some p1 =>
      rcases p1 with ⟨res1, w1⟩
      cases res1 with
      | error err =>
          refine ⟨rfl, ?_, (fun h => nomatch h)⟩
          intro outcome after events h
          injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
          subst hres hfw
          rw [hev.symm]
          exact .definedError world w1 err
      | ok b0 =>
          cases b0 with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              have hps := hintParent_spec ops otherCore into selector w1
                [.defined into selector world (.ok false) w1]
              refine ⟨hps.1, ?_, ?_⟩
              · intro outcome after events h
                obtain ⟨suffix, hsuf, htr⟩ := hps.2.1 outcome after events h
                rw [hsuf]
                exact .undefined world w1 after outcome suffix htr
              · intro hnone
                exact hparent_equiv w1 (.firstAfterUndefined w1 hdef0) (hps.2.2.mp hnone)
          | true =>
              simp only [↓reduceIte]
              rw [observe_bind, observe_bind, observe_recordHintCore]
              cases hfld0 : Models2Group4.observe
                  (JuliaLean.base.loading.Models2Group4.liftCoreAction
                    (ops.core.getfield into selector)) w1 with
              | none =>
                  dsimp only
                  exact ⟨rfl, (fun _ _ _ h => nomatch h),
                    fun _ => ⟨.ownField, w1, .ownField w1 hdef0, hfld0⟩⟩
              | some p2 =>
                  rcases p2 with ⟨res2, w2⟩
                  cases res2 with
                  | error err =>
                      refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                      intro outcome after events h
                      injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                      subst hres hfw
                      rw [hev.symm]
                      exact .fieldError world w1 w2 err
                  | ok field =>
                      dsimp only
                      by_cases hisa0 : ops.core.isa field (.leaf (ops.core.core "Module")) = true
                      · simp only [hisa0, ↓reduceIte, observe_pure]
                        refine ⟨rfl, ?_, (fun h => nomatch h)⟩
                        intro outcome after events h
                        injection h with h1; injection h1 with hres h2; injection h2 with hfw hev
                        subst hres hfw
                        rw [hev.symm]
                        exact .module world w1 w2 field _ hisa0 rfl
                      · have hisa0f : ops.core.isa field (.leaf (ops.core.core "Module")) = false :=
                          Bool.eq_false_iff.mpr hisa0
                        simp only [hisa0f, Bool.false_eq_true, ↓reduceIte]
                        have hps := hintParent_spec ops otherCore into selector w2
                          [.defined into selector world (.ok true) w1,
                           .field into selector w1 (.ok field) w2]
                        refine ⟨hps.1, ?_, ?_⟩
                        · intro outcome after events h
                          obtain ⟨suffix, hsuf, htr⟩ := hps.2.1 outcome after events h
                          rw [hsuf]
                          exact .nonModule world w1 w2 after field outcome suffix hisa0f htr
                        · intro hnone
                          exact hparent_equiv w2
                            (.firstAfterNonModule w1 w2 field (.ownField w1 hdef0) hfld0 hisa0f)
                            (hps.2.2.mp hnone)


def entriesModels2Group4 : List Entry := [
  { id := "loading-isfile-casesensitive-unix"
    juliaFile := "base/loading.jl", juliaFns := ["isfile_casesensitive(path) [Unix/non-Apple]"]
    statement := "For every input and selected dispatch, the Unix wrapper makes exactly one accessibility call; Base filters only IOError, while custom results, errors, effects and divergence pass through."
    source := "base/loading.jl:8-10,95-102; doc/src/manual/control-flow.md:790-832"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.UnixCaseSensitiveCorrect, thm := some ``JuliaLean.Proofs.base.loading.unixCaseSensitiveCorrect_proven },
  { id := "loading-isfile-casesensitive-windows"
    juliaFile := "base/loading.jl", juliaFns := ["isfile_casesensitive(path) [Windows]"]
    statement := "Windows evaluates each path operation at most once in source order with the original path, skips all path operations after accessibility false, and preserves accessibility errors and the non-Bool condition TypeError with their effects."
    source := "base/loading.jl:13-16; doc/src/manual/control-flow.md:182-193,326-335,790-832"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.WindowsCaseSensitiveCorrect, thm := some ``JuliaLean.Proofs.base.loading.windowsCaseSensitiveCorrect_proven },
  { id := "loading-isfile-casesensitive-generic"
    juliaFile := "base/loading.jl", juliaFns := ["isfile_casesensitive(path) [generic platform]"]
    statement := "The generic fallback preserves fail-fast call order, native destructuring indices and forwarded state, materializes before any, preserves accessibility errors, and returns the final any observation unchanged."
    source := "base/loading.jl:77-81; base/tuple.jl:161-172; doc/src/manual/functions.md (destructuring assignment)"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.GenericCaseSensitiveCorrect, thm := none },
  { id := "loading-core-action-adapter"
    juliaFile := "base/loading.jl", juliaFns := ["isfile_casesensitive(path) [internal Core adapter]"]
    statement := "The internal adapter preserves divergence, successful values, thrown runtime-value identity and the final world of every Core primitive action."
    source := "base/loading.jl:79; base/tuple.jl:161-172; invariant of the CoreM/loading representation adapter"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.CoreAdapterCorrect, thm := some ``JuliaLean.Proofs.base.loading.coreAdapterCorrect_proven },
  { id := "loading-isaccessibledir"
    juliaFile := "base/loading.jl", juliaFns := ["isaccessibledir(value)"]
    statement := "Over the full untyped domain, isaccessibledir calls isdir exactly once, preserves arbitrary successful values, effects and divergence, changes only IOError into false, and rethrows every other exception unchanged."
    source := "base/loading.jl:84,86-93; doc/src/manual/control-flow.md:790-832"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.AccessibleDirCorrect, thm := some ``JuliaLean.Proofs.base.loading.accessibleDirCorrect_proven },
  { id := "loading-isaccessiblefile"
    juliaFile := "base/loading.jl", juliaFns := ["isaccessiblefile(value)"]
    statement := "Over the full untyped domain, isaccessiblefile calls isfile exactly once, preserves arbitrary successful values, effects and divergence, changes only IOError into false, and rethrows every other exception unchanged."
    source := "base/loading.jl:84,95-102; doc/src/manual/control-flow.md:790-832"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.AccessibleFileCorrect, thm := some ``JuliaLean.Proofs.base.loading.accessibleFileCorrect_proven },
  { id := "loading-isaccessiblepath"
    juliaFile := "base/loading.jl", juliaFns := ["isaccessiblepath(value)"]
    statement := "Over the full untyped domain, isaccessiblepath calls ispath exactly once, preserves arbitrary successful values, effects and divergence, changes only IOError into false, and rethrows every other exception unchanged."
    source := "base/loading.jl:84,104-111; doc/src/manual/control-flow.md:790-832"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.AccessiblePathCorrect, thm := some ``JuliaLean.Proofs.base.loading.accessiblePathCorrect_proven },
  { id := "loading-sha-abstractstring"
    juliaFile := "base/loading.jl", juliaFns := ["SHA1(s::AbstractString)", "SHA256(s::AbstractString)"]
    statement := "Both SHA AbstractString constructors preserve decoder values, digest kind, recursive Base/custom dispatch sequence and terminal outcomes; initial decoder errors retain their world and divergence remains divergence."
    source := "base/loading.jl:114-124; doc/src/manual/methods.md (multiple dispatch)"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.DigestStringCorrect, thm := some ``JuliaLean.Proofs.base.loading.digestStringCorrect_proven },
  { id := "loading-sha-parse"
    juliaFile := "base/loading.jl", juliaFns := ["parse(::Type{SHA1}, s::AbstractString)", "parse(::Type{SHA256}, s::AbstractString)"]
    statement := "Both SHA parse overloads preserve selected constructor arguments, dispatch sequence and terminal outcomes; a selected custom constructor retains its complete observation without coercion."
    source := "base/loading.jl:114-125; doc/src/manual/methods.md (multiple dispatch)"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ParseDigestCorrect, thm := some ``JuliaLean.Proofs.base.loading.parseDigestCorrect_proven },
  { id := "loading-sha-tryparse"
    juliaFile := "base/loading.jl", juliaFns := ["tryparse(::Type{SHA1}, s::AbstractString)", "tryparse(::Type{SHA256}, s::AbstractString)"]
    statement := "Both SHA tryparse overloads change only ArgumentError into nothing, preserve all other results/errors, final worlds and divergence, and retain the selected dispatch sequence."
    source := "base/loading.jl:114-135; doc/src/manual/control-flow.md:790-832"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.TryParseDigestCorrect, thm := some ``JuliaLean.Proofs.base.loading.tryParseDigestCorrect_proven },
  { id := "loading-parsed-toml-default"
    juliaFile := "base/loading.jl", juliaFns := ["parsed_toml(project_file::AbstractString)"]
    statement := "The unary parsed_toml wrapper invokes selected dispatch once with the original AbstractString and exact global TOML cache/lock references, preserving the complete result, error, world and divergence."
    source := "base/loading.jl:297-299; doc/src/manual/methods.md (multiple dispatch)"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ParsedTomlDefaultCorrect, thm := some ``JuliaLean.Proofs.base.loading.parsedTomlDefaultCorrect_proven },
  { id := "loading-nothing-or-first"
    juliaFile := "base/loading.jl", juliaFns := ["_nothing_or_first(x)"]
    statement := "The internal helper returns nothing without effects for nothing input; every other value reaches selected first exactly once with its original identity and complete outcome, errors, final world and divergence preserved."
    source := "base/loading.jl:449; invariant of sentinel short-circuit and first forwarding"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.NothingOrFirstCorrect, thm := some ``JuliaLean.Proofs.base.loading.nothingOrFirstCorrect_proven },
  { id := "loading-package-get-here"
    juliaFile := "base/loading.jl", juliaFns := ["package_get_here"]
    statement := "The generic package lookup preserves dependency and constructor arguments, effects, errors and divergence; an absent dependency produces a native PkgId with no UUID and the requested name."
    source := "base/loading.jl:767-772; base/pkgid.jl:3-10; doc/src/manual/control-flow.md"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.PackageGetHereCorrect, thm := some ``JuliaLean.Proofs.base.loading.packageGetHereCorrect_proven },
  { id := "loading-package-get"
    juliaFile := "base/loading.jl", juliaFns := ["package_get"]
    statement := "The contextual package lookup checks identity with the context name before using the requested name, short-circuits true and non-Bool comparisons, and preserves selected Base/custom helper effects, errors, results and divergence."
    source := "base/loading.jl:774-780; doc/src/manual/control-flow.md"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.PackageGetCorrect, thm := some ``JuliaLean.Proofs.base.loading.packageGetCorrect_proven },
  { id := "loading-workspace-manifest"
    juliaFile := "base/loading.jl", juliaFns := ["workspace_manifest"]
    statement := "The generic workspace wrapper calls base-project resolution once, stops on nothing, and forwards any other base unchanged to manifest resolution while retaining outcomes, effects and divergence."
    source := "base/loading.jl:981-987; doc/src/manual/control-flow.md"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.WorkspaceManifestCorrect, thm := some ``JuliaLean.Proofs.base.loading.workspaceManifestCorrect_proven },
  { id := "loading-find-source-file"
    juliaFile := "base/loading.jl", juliaFns := ["find_source_file"]
    statement := "The full AbstractString source lookup preserves original object identity on early returns, exact join arguments, Bool short-circuit behavior, and all reached values/errors/worlds/divergence."
    source := "base/loading.jl:1346-1350; doc/src/manual/control-flow.md"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.FindSourceFileCorrect, thm := some ``JuliaLean.Proofs.base.loading.findSourceFileCorrect_proven },
  { id := "loading-sort-by"
    juliaFile := "base/loading.jl", juliaFns := ["sort_by"]
    statement := "The untyped index closure preserves captured vector identity, ordered indexing and mtime calls, exact named-tuple field construction, terminal outcomes and reached-callee divergence."
    source := "base/loading.jl:1401-1415; base/boot.jl:1024-1026"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.SortByCorrect, thm := some ``JuliaLean.Proofs.base.loading.sortByCorrect_proven },
  { id := "loading-sort-lt"
    juliaFile := "base/loading.jl", juliaFns := ["sort_lt"]
    statement := "The untyped comparator preserves property access and comparison order, freshly re-reads pkgimage fields after true inequality, rejects non-Bool guards and returns arbitrary less-than outcomes unchanged."
    source := "base/loading.jl:1401-1415; doc/src/manual/control-flow.md"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.SortLtCorrect, thm := some ``JuliaLean.Proofs.base.loading.sortLtCorrect_proven },
  { id := "loading-ocachefile-from-cachefile"
    juliaFile := "base/loading.jl", juliaFns := ["ocachefile_from_cachefile"]
    statement := "The generic object-cache filename wrapper removes the .ji suffix before the selected string call, preserves exact literal/extension arguments and intermediate identity, and retains terminal effects, errors and divergence."
    source := "base/loading.jl:1463; doc/src/manual/functions.md"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ObjectCachefileCorrect, thm := some ``JuliaLean.Proofs.base.loading.objectCachefileCorrect_proven },
  { id := "loading-show-cache-flags"
    juliaFile := "base/loading.jl", juliaFns := ["show(io::IO, cf::CacheFlags)"]
    statement := "All selected print/show calls preserve IO identity, exact source argument groups and native fields, conditionally print the coverage path and return the arbitrary closing-print outcome."
    source := "base/loading.jl:1954-1968,2104-2124"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ShowCacheFlagsCorrect, thm := none },
  { id := "loading-cache-flags-six"
    juliaFile := "base/loading.jl", juliaFns := ["CacheFlags(use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage)"]
    statement := "The six-argument constructor forwards all six unrestricted inputs and actual nothing to one selected seven-argument constructor, preserving all observations."
    source := "base/loading.jl:1969-1970; base/int.jl; base/bool.jl"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.CacheFlagsSixCorrect, thm := some ``JuliaLean.Proofs.base.loading.cacheFlagsSixCorrect_proven },
  { id := "loading-cache-flags-uint8"
    juliaFile := "base/loading.jl", juliaFns := ["CacheFlags(f::UInt8, coverage::Integer=0)"]
    statement := "The UInt8 constructor uses concrete native byte decoding, preserves arbitrary Integer conversion and subsequent dispatch, and the omitted-coverage overload returns independently specified fields with zero coverage."
    source := "base/loading.jl:1971-1978; base/int.jl; base/bool.jl"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.CacheFlagsUInt8Correct, thm := some ``JuliaLean.Proofs.base.loading.cacheFlagsUInt8Correct_proven },
  { id := "loading-cache-flags-uint8-path"
    juliaFile := "base/loading.jl", juliaFns := ["CacheFlags(f::UInt8, coverage::Integer, coverage_path::Union{Nothing,String})"]
    statement := "The path overload preserves the selected Base/custom inner constructor and forwards its exact result and explicit native path to the keyword call, retaining effects, errors and divergence."
    source := "base/loading.jl:2000-2001; base/int.jl; base/bool.jl"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.CacheFlagsUInt8PathCorrect, thm := some ``JuliaLean.Proofs.base.loading.cacheFlagsUInt8PathCorrect_proven },
  { id := "loading-show-image-target"
    juliaFile := "base/loading.jl", juliaFns := ["show(io::IO, it::ImageTarget)"]
    statement := "Exact unary and grouped print calls follow concrete native emptiness and promoted integer comparisons; the final conditional returns nothing or the arbitrary final print result, preserving errors, state and divergence."
    source := "base/loading.jl:2147-2154,2186-2201"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ShowImageTargetCorrect, thm := none },
  { id := "loading-parse-image-target"
    juliaFile := "base/loading.jl", juliaFns := ["parse_image_target"]
    statement := "Preserve all generic read results, separate native-eight multiplications, explicit String calls, both complete ordered foreign conversion/ABI-check/root regions, and arbitrary final ImageTarget constructor result with exact errors, worlds and divergence."
    source := "base/loading.jl:2156-2169; base/c.jl:405-419; doc/src/manual/calling-c-and-fortran-code.md:246-276,710-727"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ParseImageTargetCorrect, thm := none },
  { id := "loading-include-dependency-internal"
    juliaFile := "base/loading.jl", juliaFns := ["_include_dependency"]
    statement := "Read the captured native Ref field x before selected dependency recording and forward the original captures, module, path and keyword flags, preserving outcomes, worlds, defaults and divergence."
    source := "base/loading.jl:2677-2680; base/refvalue.jl:59"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.IncludeDependencyInternalCorrect, thm := some ``JuliaLean.Proofs.base.loading.includeDependencyInternalCorrect_proven },
  { id := "loading-include-mapexprs"
    juliaFile := "base/loading.jl", juliaFns := ["include_mapexprs"]
    statement := "Execute the installed module-root traversal, then exact definedness/global-read/typeassert protocol; preserve absent binding, object identity, failure worlds, exact exception payloads and divergence."
    source := "base/loading.jl:2758-2762; base/runtime_internals.jl; base/boot.jl"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.IncludeMapexprsCorrect, thm := none },
  { id := "loading-include-dependency-public"
    juliaFile := "base/loading.jl", juliaFns := ["include_dependency"]
    statement := "Selected Base/custom delegation uses Main, the original path and track-content flag, enables directory paths, preserves failures and divergence, and discards every successful result in favor of actual nothing."
    source := "base/loading.jl:2781-2784"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.IncludeDependencyPublicCorrect, thm := some ``JuliaLean.Proofs.base.loading.includeDependencyPublicCorrect_proven },
  { id := "loading-show-precompilable-error"
    juliaFile := "base/loading.jl", juliaFns := ["show(io::IO, ex::PrecompilableError)"]
    statement := "One selected print receives the original IO and exact 104-byte diagnostic; every arbitrary return, exception, world change and divergence is the enclosing show observation."
    source := "base/loading.jl:2788-2790"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ShowPrecompilableErrorCorrect, thm := some ``JuliaLean.Proofs.base.loading.showPrecompilableErrorCorrect_proven },
  { id := "loading-wrapped-precompilable-error"
    juliaFile := "base/loading.jl", juliaFns := ["precompilableerror(ex::WrappedException)"]
    statement := "Every wrapped entry reads its actual error property before selected classification; Base wrapped results recurse without fuel, native terminal branches use installed bodies, and arbitrary custom values/errors/worlds/divergence are retained."
    source := "base/loading.jl:2791-2793"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.WrappedPrecompilableCorrect, thm := none },
  { id := "loading-check-for-hint"
    juliaFile := "base/loading.jl", juliaFns := ["check_for_hint"]
    statement := "Use full-domain Core definedness/getfield/isa and two separate selected parentmodule calls; preserve original selector, short-circuit behavior, exact native hint tuples, errors, worlds and reached-callee divergence."
    source := "base/loading.jl:2855-2865; base/docs/basedocs.jl:3014-3056"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.CheckForHintCorrect, thm := some ``JuliaLean.Proofs.base.loading.checkForHintCorrect_proven },
  { id := "loading-include-string-identity"
    juliaFile := "base/loading.jl", juliaFns := ["include_string(m::Module, txt::AbstractString, fname::AbstractString=\"string\")"]
    statement := "Explicit entry forwards identity/original objects once; optional entry inserts the exact string literal and performs actual Base/custom three-argument dispatch, preserving every selected-call observation."
    source := "base/loading.jl:3472-3473; doc/src/manual/methods.md:885-911"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.IncludeStringIdentityCorrect, thm := some ``JuliaLean.Proofs.base.loading.includeStringIdentityCorrect_proven },
  { id := "loading-package-loaded-error"
    juliaFile := "base/loading.jl", juliaFns := ["check_package_module_loaded_error"]
    statement := "Read the package name twice before interpolation, preserve both distinct values and exact literal segments, then pass the actual message to selected error without restricting its result or discarding errors, worlds or divergence."
    source := "base/loading.jl:3672-3676; doc/src/manual/strings.md:169-177"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.PackageLoadedErrorCorrect, thm := some ``JuliaLean.Proofs.base.loading.packageLoadedErrorCorrect_proven },
  { id := "loading-preferences-blob-stream"
    juliaFile := "base/loading.jl", juliaFns := ["preferences_blob(f::IO, cachefile::AbstractString)"]
    statement := "Call the selected parser with original IO/path then selected indexing on its actual return at native Int five, with exact fail-fast ordering, unrestricted results, failure worlds and reached-callee divergence."
    source := "base/loading.jl:4370"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.PreferenceBlobStreamCorrect, thm := some ``JuliaLean.Proofs.base.loading.preferenceBlobStreamCorrect_proven },
  { id := "loading-filter-preferences"
    juliaFile := "base/loading.jl", juliaFns := ["filter_preferences"]
    statement := "Preserve the original dictionary alias for nothing keys; otherwise call selected get with the exact Dict type factory/dictionary/arbitrary key, then enforce native typeassert with exact TypeError payload and no rollback."
    source := "base/loading.jl:4490-4496; base/boot.jl:249-252; doc/src/manual/types.md"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.FilterPreferencesCorrect, thm := some ``JuliaLean.Proofs.base.loading.filterPreferencesCorrect_proven },
  { id := "loading-toml-egal-identity"
    juliaFile := "base/loading.jl", juliaFns := ["toml_egal(@nospecialize(A), @nospecialize(B))"]
    statement := "Universal heterogeneous identity binds the installed method to Core.same on the actual ordered input pair; primitive-locality and Boolean anchors retain identity without assuming equality laws."
    source := "base/loading.jl:4863-4866"
    status := .proven, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.TomlEgalIdentityCorrect, thm := some ``JuliaLean.Proofs.base.loading.tomlEgalIdentityCorrect_proven },
  { id := "loading-toml-egal-dict"
    juliaFile := "base/loading.jl", juliaFns := ["toml_egal(A::AbstractDict, B::AbstractDict)"]
    statement := "Actual iterator recursion preserves native IdDict/Int checks, raw fields, exact comparator identity, arbitrary selected membership/negation, errors, state and realized finite-trace/divergence correspondence."
    source := "base/loading.jl:4876-4883; doc/src/manual/interfaces.md:29-54"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.TomlEgalDictCorrect, thm := none },
  { id := "loading-expand-compiler-path"
    juliaFile := "base/loading.jl", juliaFns := ["expand_compiler_path"]
    statement := "Preserve full generic indexing, native global String arguments, lastindex/colon/slice calls, exact native prefix tuple and Base.iterate/Core.tuple splat identities; retain arbitrary results, first failures, state and reached-callee divergence."
    source := "base/loading.jl:5196-5198; base/boot.jl:1256-1257; doc/src/manual/functions.md"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.ExpandCompilerPathCorrect, thm := none },
  { id := "loading-compiler-chi"
    juliaFile := "base/loading.jl", juliaFns := ["compiler_chi"]
    statement := "All native tuple arities and element parameterizations retain Base/custom expansion selection; actual Base expansion runs, its exact result reaches selected header construction, and errors/worlds/divergence are preserved."
    source := "base/loading.jl:5199; doc/src/devdocs/types.md:250-318"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.CompilerChiCorrect, thm := none },
  { id := "loading-isprecompilable-function"
    juliaFile := "base/loading.jl", juliaFns := ["isprecompilable(@nospecialize(f), @nospecialize(argtypes::Tuple))"]
    statement := "Full native tuple-domain signature construction preserves selected Core.Typeof, installed Base Typeof, native type application and splat, exact function identities, Base C-query versus unrestricted custom return, errors, failure worlds and reached divergence; the raw Core adapter law is independent."
    source := "base/loading.jl:5207-5213"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.IsPrecompilableFunctionCorrect, thm := none },
  { id := "loading-precompile-function"
    juliaFile := "base/loading.jl", juliaFns := ["precompile(@nospecialize(f), @nospecialize(argtypes::Tuple))"]
    statement := "Selected Core.Typeof and actual native signature construction precede the exact selected unary precompile call; arbitrary results, errors, state and reached divergence are preserved over every bounded native tuple, with an independent raw Core adapter invariant."
    source := "base/loading.jl:5220-5222"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.PrecompileFunctionCorrect, thm := none },
  { id := "loading-precompile-function-method"
    juliaFile := "base/loading.jl", juliaFns := ["precompile(@nospecialize(f), @nospecialize(argtypes::Tuple), m::Method)"]
    statement := "Full selected Typeof and native type-splat construction preserve all tuple values and errors, then forward the exact signature and original Method reference to selected precompile; arbitrary returns, failure worlds and reached divergence obey the independent protocol."
    source := "base/loading.jl:5244-5246"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.PrecompileFunctionMethodCorrect, thm := none },
  { id := "loading-precompile-type-method"
    juliaFile := "base/loading.jl", juliaFns := ["precompile(@nospecialize(argt::Type), m::Method)"]
    statement := "The concrete Method.sig read, two-target destructuring, exact Base.Compiler.specialize_method identity and final selected precompile preserve all operands, arbitrary results, errors, failure worlds and reached divergence in the independent nine-operation protocol."
    source := "base/loading.jl:5248-5252"
    status := .todo, prop := ``JuliaLean.Proofs.base.loading.Models2Group4.PrecompileTypeMethodCorrect, thm := none }
]
end JuliaLean.Proofs.base.loading


namespace JuliaLean.Proofs.base.loading.SourceCoverage

open JuliaLean JuliaLean.base.loading JuliaLean.Registry

/-- A direct precompilation refusal is recognized without inspecting any payload. -/
def DirectPrecompilableRecognized : Prop :=
  ∀ ex : PrecompilableError, precompilableerror_precompilable ex = true

/-- The catch-all method does not classify an unrelated exception as a refusal. -/
def UnrelatedExceptionNotPrecompilable : Prop :=
  ∀ (Exception : Type) (ex : Exception), precompilableerror_other ex = false

/-- An absent reason collector cannot accumulate a rejection. -/
def AbsentReasonCollector : Prop :=
  ∀ reason : Bytes, record_reason_nothing reason = ()

/-- With no reason collector, both verbosity settings produce an empty message. -/
def AbsentReasonsHaveNoMessage : Prop :=
  ∀ full : Bool, (list_reasons_nothing full).length = 0

/-- Syntax editions 13 through 268 have consecutive cache codes, independently of major version. -/
def CacheEditionConsecutive : Prop :=
  ∀ major minor : JInt64, 13 ≤ minor.val → minor.val ≤ 268 →
    (cache_edition (major, minor)).val = minor.val - 13

/-- A nonzero C compilation-admission result means admissible, including negative C integers.
The C query's errors, post-state and nontermination are retained. -/
def CompilabilityRuntimeResult : Prop :=
  ∀ (X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance : Type)
    (o : LOps X Y E D CI CF V)
    (ops : CompilerMethodOps o Function FunctionType ArgTypes Signature Method StaticParams MethodInstance)
    (argtype : Signature) (before : World X D CI CF),
    match StateT.run (ExceptT.run (ops.isCompilable argtype)) before with
    | none => StateT.run (ExceptT.run (isprecompilable_type o ops argtype)) before = none
    | some (.error error, after) =>
        StateT.run (ExceptT.run (isprecompilable_type o ops argtype)) before = some (.error error, after)
    | some (.ok flag, after) =>
        ∃ answer, StateT.run (ExceptT.run (isprecompilable_type o ops argtype)) before =
          some (.ok answer, after) ∧ (answer = true ↔ flag.val ≠ 0)

/-- The MethodInstance overload reports success after its C compilation call returns;
explicit worlds bypass observation of the current world. -/
def ExplicitMethodWorldSuccess : Prop :=
  ∀ (X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance : Type)
    (o : LOps X Y E D CI CF V)
    (ops : CompilerMethodOps o Function FunctionType ArgTypes Signature Method StaticParams MethodInstance)
    (mi : MethodInstance) (world : CacheU64) (before after : World X D CI CF),
    StateT.run (ExceptT.run (ops.compileMethodInstance mi world)) before = some (.ok (), after) →
    StateT.run (ExceptT.run (precompile_method_instance o ops mi (some world))) before =
      some (.ok true, after)

theorem directPrecompilableRecognized_proven : DirectPrecompilableRecognized := by
  intro ex
  rfl

theorem unrelatedExceptionNotPrecompilable_proven : UnrelatedExceptionNotPrecompilable := by
  intro Exception ex
  rfl

theorem absentReasonCollector_proven : AbsentReasonCollector := by
  intro reason
  rfl

theorem absentReasonsHaveNoMessage_proven : AbsentReasonsHaveNoMessage := by
  intro full
  rfl

theorem cacheEditionConsecutive_proven : CacheEditionConsecutive := by
  intro major minor lower upper
  have difference :
      (JuliaLean.base.int.sub minor (i64 13)).val = minor.val - 13 := by
    rw [JuliaLean.base.int.sub, JuliaLean.Proofs.base.int.sub_int_val]
    change wrapInt .i64 (minor.val - 13) = minor.val - 13
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ minor.val - 13 ∧ minor.val - 13 ≤ 9223372036854775807
    omega
  dsimp only [cache_edition]
  rw [difference]
  have nonnegative : ¬minor.val - 13 < 0 := by omega
  have fits : ¬minor.val - 13 > 255 := by omega
  simp only [nonnegative, fits, ite_false]
  change wrapInt .u8 (minor.val - 13) = minor.val - 13
  apply wrapInt_of_inRange
  change 0 ≤ minor.val - 13 ∧ minor.val - 13 ≤ 255
  omega

private theorem action_bind_run {X Y E D CI CF V α β : Type} {o : LOps X Y E D CI CF V}
    (act : LM o α) (f : α → LM o β) (w : World X D CI CF) :
    StateT.run (ExceptT.run (act >>= f)) w =
      match StateT.run (ExceptT.run act) w with
      | none => none
      | some (.error e, w') => some (.error e, w')
      | some (.ok a, w') => StateT.run (ExceptT.run (f a)) w' := by
  simp only [ExceptT.run, StateT.run, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    StateT.bind, Option.bind]
  cases act w with
  | none => rfl
  | some p => rcases p with ⟨r, w'⟩; cases r <;> rfl

theorem compilabilityRuntimeResult_proven : CompilabilityRuntimeResult := by
  intro X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance o ops argtype before
  unfold isprecompilable_type
  rw [action_bind_run]
  cases observed : StateT.run (ExceptT.run (ops.isCompilable argtype)) before with
  | none => rfl
  | some pair =>
    rcases pair with ⟨result, after⟩
    cases result with
    | error error => rfl
    | ok flag =>
      refine ⟨flag.val != 0, rfl, ?_⟩
      simp

theorem explicitMethodWorldSuccess_proven : ExplicitMethodWorldSuccess := by
  intro X Y E D CI CF V Function FunctionType ArgTypes Signature Method StaticParams MethodInstance o ops mi world before after success
  unfold precompile_method_instance
  change StateT.run (ExceptT.run (ops.compileMethodInstance mi world >>= fun _ => pure true)) before = _
  rw [action_bind_run, success]
  rfl


def entries : List Entry := [
  { id := "loading-direct-precompilable-recognized", juliaFile := "base/loading.jl"
    juliaFns := ["precompilableerror(::PrecompilableError)"]
    statement := "A direct PrecompilableError is recognized as a precompilation refusal."
    source := "base/loading.jl:2791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``DirectPrecompilableRecognized, thm := some ``directPrecompilableRecognized_proven },
  { id := "loading-unrelated-exception-not-precompilable", juliaFile := "base/loading.jl"
    juliaFns := ["precompilableerror(@nospecialize ex)"]
    statement := "The catch-all precompilableerror method returns false for every exception passed to that method."
    source := "base/loading.jl:2793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnrelatedExceptionNotPrecompilable, thm := some ``unrelatedExceptionNotPrecompilable_proven },
  { id := "loading-absent-reason-collector", juliaFile := "base/loading.jl"
    juliaFns := ["record_reason(::Nothing, ::Symbol)"]
    statement := "An absent reason collector accepts any rejection reason and returns nothing."
    source := "base/loading.jl:4695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``AbsentReasonCollector, thm := some ``absentReasonCollector_proven },
  { id := "loading-absent-reasons-no-message", juliaFile := "base/loading.jl"
    juliaFns := ["list_reasons(::Nothing; full::Bool=false)"]
    statement := "An absent reason collector produces an empty message for either verbosity setting."
    source := "base/loading.jl:4768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``AbsentReasonsHaveNoMessage, thm := some ``absentReasonsHaveNoMessage_proven },
  { id := "loading-cache-edition-consecutive", juliaFile := "base/loading.jl"
    juliaFns := ["cache_edition(::Tuple{Int,Int})"]
    statement := "Syntax editions 13 through 268 have consecutive cache codes 0 through 255, independently of major version."
    source := "base/loading.jl:4859-4861 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CacheEditionConsecutive, thm := some ``cacheEditionConsecutive_proven },
  { id := "loading-compilability-runtime-result", juliaFile := "base/loading.jl"
    juliaFns := ["isprecompilable(@nospecialize(argt::Type))"]
    statement := "Zero C admission status means false and every nonzero status means true; query errors, state and nontermination are preserved."
    source := "base/loading.jl:5211-5213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CompilabilityRuntimeResult, thm := some ``compilabilityRuntimeResult_proven },
  { id := "loading-explicit-method-world-success", juliaFile := "base/loading.jl"
    juliaFns := ["precompile(mi::MethodInstance, world::UInt=get_world_counter())"]
    statement := "With an explicit world, the MethodInstance overload returns true after successful C compilation and retains that call's post-state."
    source := "base/loading.jl:5234-5235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ExplicitMethodWorldSuccess, thm := some ``explicitMethodWorldSuccess_proven }
]

end JuliaLean.Proofs.base.loading.SourceCoverage
