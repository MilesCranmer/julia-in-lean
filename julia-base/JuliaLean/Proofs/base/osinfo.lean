import JuliaLean.base.osinfo
import JuliaLean.base.strings.io
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.osinfo

open JuliaLean.Registry

namespace Round1

open JuliaLean JuliaLean.base.osinfo
open JuliaLean.base.strings.io (JuliaSymbol)

/-- An injective representation of every Symbol byte name in the installed
String carrier. Each byte becomes the Unicode character with the same numeric
value; no decoding, replacement, normalization, kernel-name lookup, or predicate
evaluation occurs. In particular, malformed UTF-8 remains represented.

Every literal compared by the installed OS predicates is ASCII. This embedding
fixes ASCII strings and reflects equality with each such literal, so it preserves
all Boolean observations used here, including the successful isunix branch.
It is not Julia's String(::Symbol) conversion and makes no claim about the
original-byte payload of an unknown-system error.
-/
def symbolClassifierCarrier (os : JuliaSymbol) : String :=
  String.ofList (os.name.map (fun byte => Char.ofNat byte.toNat))

/-- A Julia Symbol cannot contain a NUL byte. Names need not be valid UTF-8.
Julia source: base/boot.jl:856-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Existing model: base/boot.lean:1950-1957; base/strings/io.lean:34-35.
-/
def IsSymbolName (os : JuliaSymbol) : Prop :=
  ∀ byte ∈ os.name, byte ≠ (0 : UInt8)

/-- Linux, Apple and FreeBSD are mutually exclusive subsets of Unix for every
constructible Symbol name, including names containing malformed UTF-8 bytes.
Julia source: base/osinfo.jl:29-43,51,64,78,136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/handling-operating-system-variation.md:15;
base/osinfo.jl:23-28,45-50,59-62,66-77,130-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027

This property states only the documented family relationship. It does not state
exact kernel-name recognition, unknown-system error payloads, native KERNEL
initialization, the generated zero-argument methods, or WSL detection. The
quantified name is unrestricted apart from the Symbol NUL invariant. The carrier
and classifier models perform no Julia Int length/index/count arithmetic.
-/
def UnixFamilyRelationshipCorrect : Prop :=
  ∀ (os : JuliaSymbol), IsSymbolName os →
    let name := symbolClassifierCarrier os
    (¬ (islinux name = true ∧ isapple name = true)) ∧
    (¬ (islinux name = true ∧ isfreebsd name = true)) ∧
    (¬ (isapple name = true ∧ isfreebsd name = true)) ∧
    ((islinux name = true ∨ isapple name = true ∨ isfreebsd name = true) →
      isunix name = .ok true)

/-- The named BSD subfamilies form a disjoint partition, and the documented
non-Apple guard selects exactly the four non-Apple BSD subfamilies.
Julia source: base/osinfo.jl:64,78,92,106,120,136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/osinfo.jl:53-77,80-119,130-135;
doc/src/manual/handling-operating-system-variation.md:15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027

The cardinalities require mutually exclusive subfamilies, which is stronger than
the OR expression defining isbsd. An overlapping subtype implementation can
violate this property even while preserving that OR expression unchanged. The
same full byte-name representation and NUL invariant apply; this is a relation
among classifier observations rather than a native kernel-identification claim.
-/
def BsdFamilyPartitionCorrect : Prop :=
  ∀ (os : JuliaSymbol), IsSymbolName os →
    let name := symbolClassifierCarrier os
    let nonApple := [isfreebsd name, isopenbsd name, isnetbsd name, isdragonfly name]
    (nonApple ++ [isapple name]).count true =
      (if isbsd name then (1 : Nat) else 0) ∧
    nonApple.count true =
      (if isbsd name && !isapple name then (1 : Nat) else 0)

/-- A kernel name belongs to at most one of the Windows, Linux, BSD and JSVM
families.
Julia source: base/osinfo.jl:29-43,51,64,128,147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/osinfo.jl:23-28,45-63,122-146;
doc/src/manual/handling-operating-system-variation.md:3-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027

This is a cross-family invariant of the documented kernel classification, not a
claim about the host OS outside a virtual machine. It uses the same complete
Symbol byte domain and does not supply or inspect an expected classification.
-/
def KernelFamilyExclusionCorrect : Prop :=
  ∀ (os : JuliaSymbol), IsSymbolName os →
    let name := symbolClassifierCarrier os
    [iswindows name, islinux name, isbsd name, isjsvm name].count true ≤ 1

end Round1

end JuliaLean.Proofs.base.osinfo

section
namespace JuliaLean.ChatGPT.Batch4.Group10
open JuliaLean.base.osinfo JuliaLean.Proofs.base.osinfo.Round1

theorem OsinfoUnixFamilyRelations_proven : JuliaLean.Proofs.base.osinfo.Round1.UnixFamilyRelationshipCorrect := by
  intro os _
  dsimp only
  by_cases h0 : symbolClassifierCarrier os = "Linux"
  · rw [h0]
    decide
  by_cases h1 : symbolClassifierCarrier os = "Apple"
  · rw [h1]
    decide
  by_cases h2 : symbolClassifierCarrier os = "Darwin"
  · rw [h2]
    decide
  by_cases h3 : symbolClassifierCarrier os = "FreeBSD"
  · rw [h3]
    decide
  simp [islinux, isapple, isfreebsd, isopenbsd, isnetbsd, isdragonfly, iswindows, isjsvm, isbsd, isunix, h0, h1, h2, h3]

theorem OsinfoBsdFamilyPartition_proven : JuliaLean.Proofs.base.osinfo.Round1.BsdFamilyPartitionCorrect := by
  intro os _
  dsimp only
  by_cases h0 : symbolClassifierCarrier os = "FreeBSD"
  · rw [h0]
    decide
  by_cases h1 : symbolClassifierCarrier os = "OpenBSD"
  · rw [h1]
    decide
  by_cases h2 : symbolClassifierCarrier os = "NetBSD"
  · rw [h2]
    decide
  by_cases h3 : symbolClassifierCarrier os = "DragonFly"
  · rw [h3]
    decide
  by_cases h4 : symbolClassifierCarrier os = "Apple"
  · rw [h4]
    decide
  by_cases h5 : symbolClassifierCarrier os = "Darwin"
  · rw [h5]
    decide
  simp [islinux, isapple, isfreebsd, isopenbsd, isnetbsd, isdragonfly, iswindows, isjsvm, isbsd, isunix, h0, h1, h2, h3, h4, h5]

theorem OsinfoKernelFamilySeparation_proven : JuliaLean.Proofs.base.osinfo.Round1.KernelFamilyExclusionCorrect := by
  intro os _
  dsimp only
  by_cases h0 : symbolClassifierCarrier os = "Windows"
  · rw [h0]
    decide
  by_cases h1 : symbolClassifierCarrier os = "NT"
  · rw [h1]
    decide
  by_cases h2 : symbolClassifierCarrier os = "Linux"
  · rw [h2]
    decide
  by_cases h3 : symbolClassifierCarrier os = "FreeBSD"
  · rw [h3]
    decide
  by_cases h4 : symbolClassifierCarrier os = "OpenBSD"
  · rw [h4]
    decide
  by_cases h5 : symbolClassifierCarrier os = "NetBSD"
  · rw [h5]
    decide
  by_cases h6 : symbolClassifierCarrier os = "DragonFly"
  · rw [h6]
    decide
  by_cases h7 : symbolClassifierCarrier os = "Apple"
  · rw [h7]
    decide
  by_cases h8 : symbolClassifierCarrier os = "Darwin"
  · rw [h8]
    decide
  by_cases h9 : symbolClassifierCarrier os = "Emscripten"
  · rw [h9]
    decide
  simp [islinux, isapple, isfreebsd, isopenbsd, isnetbsd, isdragonfly, iswindows, isjsvm, isbsd, isunix, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

end JuliaLean.ChatGPT.Batch4.Group10
end

namespace JuliaLean.Proofs.base.osinfo
def entries : List JuliaLean.Registry.Entry := [
  { id := "osinfo-unix-family-relations", juliaFile := "base/osinfo.jl",
    juliaFns := ["islinux(::Symbol)", "isapple(::Symbol)", "isfreebsd(::Symbol)", "isunix(::Symbol)"],
    statement := "For every Symbol name, Linux, Apple and FreeBSD are pairwise exclusive, and each of them is Unix.",
    source := "doc/src/manual/handling-operating-system-variation.md:15; base/osinfo.jl:29-43,51,64,78,136", status := .proven,
    prop := ``JuliaLean.Proofs.base.osinfo.Round1.UnixFamilyRelationshipCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group10.OsinfoUnixFamilyRelations_proven },
  { id := "osinfo-bsd-family-partition", juliaFile := "base/osinfo.jl",
    juliaFns := ["isbsd(::Symbol)", "isfreebsd(::Symbol)", "isopenbsd(::Symbol)", "isnetbsd(::Symbol)", "isdragonfly(::Symbol)", "isapple(::Symbol)"],
    statement := "For every Symbol name, FreeBSD, OpenBSD, NetBSD, DragonFly and Apple are mutually exclusive, isbsd holds exactly when one of them does, and isbsd without isapple selects exactly the four non-Apple families.",
    source := "base/osinfo.jl:53-136 (isbsd and family docstrings)", status := .proven,
    prop := ``JuliaLean.Proofs.base.osinfo.Round1.BsdFamilyPartitionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group10.OsinfoBsdFamilyPartition_proven },
  { id := "osinfo-kernel-family-separation", juliaFile := "base/osinfo.jl",
    juliaFns := ["iswindows(::Symbol)", "islinux(::Symbol)", "isbsd(::Symbol)", "isjsvm(::Symbol)"],
    statement := "For every Symbol name, at most one of the Windows, Linux, BSD and JavaScript-VM family predicates holds.",
    source := "base/osinfo.jl:23-147; doc/src/manual/handling-operating-system-variation.md:3-15", status := .proven,
    prop := ``JuliaLean.Proofs.base.osinfo.Round1.KernelFamilyExclusionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group10.OsinfoKernelFamilySeparation_proven }
]

end JuliaLean.Proofs.base.osinfo

namespace JuliaLean.Proofs.base.osinfo

open JuliaLean JuliaLean.base.osinfo
open JuliaLean.base.io (M)

/-- OS predicates recognize precisely the documented kernel names; successful
cached initialization preserves the same classification for zero-argument calls.
WSL probes require Linux and stop after the first successful filesystem probe. -/
def LegacyOsPredicates : Prop :=
  (∀ os : String,
    (islinux os = true ↔ os = "Linux") ∧
    (isfreebsd os = true ↔ os = "FreeBSD") ∧
    (isopenbsd os = true ↔ os = "OpenBSD") ∧
    (isnetbsd os = true ↔ os = "NetBSD") ∧
    (isdragonfly os = true ↔ os = "DragonFly") ∧
    (iswindows os = true ↔ os = "Windows" ∨ os = "NT") ∧
    (isapple os = true ↔ os = "Apple" ∨ os = "Darwin") ∧
    (isjsvm os = true ↔ os = "Emscripten")) ∧
  (∀ os : String, (∃ b, isunix os = .ok b) ↔
    os ∈ ["Linux", "FreeBSD", "OpenBSD", "NetBSD", "DragonFly", "Apple", "Darwin", "Windows", "NT", "Emscripten"]) ∧
  (∀ os cached, buildPredicates os = .ok cached →
    [isunixDefault cached, islinuxDefault cached, isbsdDefault cached,
      isappleDefault cached, iswindowsDefault cached, isfreebsdDefault cached,
      isopenbsdDefault cached, isnetbsdDefault cached, isdragonflyDefault cached,
      isjsvmDefault cached] =
    [decide (os ≠ "Windows" ∧ os ≠ "NT"), decide (os = "Linux"),
      decide (os ∈ ["FreeBSD", "OpenBSD", "NetBSD", "DragonFly", "Apple", "Darwin"]),
      decide (os = "Apple" ∨ os = "Darwin"), decide (os = "Windows" ∨ os = "NT"),
      decide (os = "FreeBSD"), decide (os = "OpenBSD"), decide (os = "NetBSD"),
      decide (os = "DragonFly"), decide (os = "Emscripten")]) ∧
  (∀ (World : Type) (file dir : String → M World Bool) (before : World),
    detectwsl false file dir before = some (.ok (false, before)) ∧
    (∀ after, file "/proc/sys/fs/binfmt_misc/WSLInterop" before = some (.ok (true, after)) →
      detectwsl true file dir before = some (.ok (true, after))) ∧
    (∀ after, file "/proc/sys/fs/binfmt_misc/WSLInterop" before = some (.ok (false, after)) →
      detectwsl true file dir before = dir "/run/WSL" after))

theorem legacyOsPredicates_proven : LegacyOsPredicates := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro os
    simp [islinux, isfreebsd, isopenbsd, isnetbsd, isdragonfly, iswindows, isapple, isjsvm]
  · intro os
    by_cases known : os ∈ ["Linux", "FreeBSD", "OpenBSD", "NetBSD", "DragonFly",
      "Apple", "Darwin", "Windows", "NT", "Emscripten"]
    · simp at known
      rcases known with h | h | h | h | h | h | h | h | h | h <;>
        subst os <;> decide
    · simp at known
      simp_all [isunix, iswindows, islinux, isbsd, isfreebsd, isopenbsd,
        isnetbsd, isdragonfly, isapple, pure, Except.pure, throw, throwThe]
  · intro os cached run
    by_cases known : os ∈ ["Linux", "FreeBSD", "OpenBSD", "NetBSD", "DragonFly",
      "Apple", "Darwin", "Windows", "NT", "Emscripten"]
    · simp at known
      rcases known with h | h | h | h | h | h | h | h | h | h <;> subst os <;>
        simp_all [buildPredicates, isunix, iswindows, islinux, isbsd, isfreebsd,
          isopenbsd, isnetbsd, isdragonfly, isapple, isjsvm, bind, Except.bind,
          pure, Except.pure, isunixDefault, islinuxDefault, isbsdDefault,
          isappleDefault, iswindowsDefault, isfreebsdDefault, isopenbsdDefault,
          isnetbsdDefault, isdragonflyDefault, isjsvmDefault] <;> cases run <;> decide
    · simp at known
      simp_all [buildPredicates, isunix, iswindows, islinux, isbsd, isfreebsd,
        isopenbsd, isnetbsd, isdragonfly, isapple, isjsvm, bind, Except.bind,
        pure, Except.pure, throw, throwThe]
  · intro World file dir before
    refine ⟨rfl, ?_, ?_⟩
    · intro after run
      simp [detectwsl, bind, pure, run]
    · intro after run
      simp [detectwsl, bind, pure, run]

def entriesLegacyRetired : List JuliaLean.Registry.Entry := [
  { id := "runtimecov-osinfo", juliaFile := "base/osinfo.jl",
    juliaFns := ["KERNEL", "isunix", "islinux", "isbsd", "isfreebsd", "isopenbsd", "isnetbsd",
      "isdragonfly", "iswindows", "isapple", "isjsvm", "detectwsl", "$f()"],
    statement := "OS predicates match exactly their kernel symbols, isunix throws on unknown systems, detectwsl needs Linux plus a WSL marker, and the generated zero-argument predicates apply their predicate to KERNEL.",
    source := "base/osinfo.jl:1-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .proven, prop := ``LegacyOsPredicates, thm := some ``legacyOsPredicates_proven,
    notes := "Uses the installed String kernel-name carrier directly. No old Sym carrier or private hostPredicate wrapper is retained; filesystem effects are quantified at the existing IO boundary." }
]

end JuliaLean.Proofs.base.osinfo
