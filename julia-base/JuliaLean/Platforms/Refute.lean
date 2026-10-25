import JuliaLean.Platforms.Lemmas

/-!
# Refuted properties of `base/binaryplatforms.jl`

Every counterexample uses ASCII strings only, so `lowercase` is `asciiLower`
(extended by the identity), which satisfies `LcSpec`.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber)

/-! ## `platforms-triplet-roundtrip`: an empty tag value -/

def emptyTagPlatform : Platform :=
  ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "linux"), (s% "foo", []), (s% "libc", s% "glibc")], []⟩

theorem emptyTag_ctor :
    platform asciiLower (s% "x86_64") (s% "linux") [(s% "foo", .str [])] true = .ok emptyTagPlatform := by
  decide +kernel

theorem emptyTag_triplet : triplet emptyTagPlatform = .ok (s% "x86_64-linux-gnu-foo+") := by decide +kernel

theorem emptyTag_parse :
    parsePlatform asciiLower false (s% "x86_64-linux-gnu-foo+") =
      .error (.argumentError "not an officially supported platform") := by decide +kernel

theorem tripletRoundtrip_refuted : ¬ TripletRoundtrip := by
  intro h
  obtain ⟨t, q, ht, hq, _⟩ := h asciiLower asciiLower_spec _ _ _ _ emptyTag_ctor
  rw [emptyTag_triplet] at ht
  cases ht
  rw [emptyTag_parse] at hq
  cases hq

/-! ## `platforms-openbsd-os-version` -/

def openbsdPlatform : Platform :=
  ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "openbsd"), (s% "os_version", s% "7.4.0")], []⟩

def openbsdBare : Platform := ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "openbsd")], []⟩

theorem openbsd_parse : parsePlatform asciiLower false (s% "x86_64-unknown-openbsd7.4") = .ok openbsdPlatform := by
  decide +kernel

theorem openbsd_triplet : triplet openbsdPlatform = .ok (s% "x86_64-unknown-openbsd") := by decide +kernel

theorem openbsd_reparse : parsePlatform asciiLower false (s% "x86_64-unknown-openbsd") = .ok openbsdBare := by
  decide +kernel

theorem parseTripletParse_refuted : ¬ ParseTripletParse := by
  intro h
  obtain ⟨t, q, ht, hq, heq⟩ := h asciiLower asciiLower_spec _ _ openbsd_parse
  rw [openbsd_triplet] at ht
  cases ht
  rw [openbsd_reparse] at hq
  cases hq
  revert heq
  decide

/-! ## `platforms-validate-os-version` -/

def badOsVersionPlatform : Platform :=
  ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "macos"), (s% "os_version", s% "foo")], []⟩

theorem badOsVersion_ctor :
    platform asciiLower (s% "x86_64") (s% "macos") [(s% "os_version", .str (s% "foo"))] true =
      .ok badOsVersionPlatform := by decide +kernel

theorem badOsVersion_triplet :
    triplet badOsVersionPlatform = .error (.argumentError "invalid version string") := by decide +kernel

theorem strictTripletTotal_refuted : ¬ StrictTripletTotal := by
  intro h
  obtain ⟨t, ht⟩ := h asciiLower asciiLower_spec _ _ _ _ badOsVersion_ctor
  rw [badOsVersion_triplet] at ht
  cases ht

/-! ## `platforms-match-reflexive` -/

def badJuliaVersionPlatform : Platform :=
  ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "linux"), (s% "julia_version", s% "foo"), (s% "libc", s% "glibc")],
   [(s% "julia_version", .juliaMinor)]⟩

theorem badJuliaVersion_ctor :
    platform asciiLower (s% "x86_64") (s% "linux") [(s% "julia_version", .str (s% "foo"))] true =
      .ok badJuliaVersionPlatform := by decide +kernel

/-- Any user-strategy semantics (none is used: the platforms have only built-in strategies). -/
def noUser : UserSem := fun _ _ _ _ _ => .ok true

theorem badJuliaVersion_match :
    platformsMatch noUser (unionOrder badJuliaVersionPlatform badJuliaVersionPlatform)
      badJuliaVersionPlatform badJuliaVersionPlatform = .error (.argumentError "invalid version string") := by
  decide +kernel

theorem matchReflexive_refuted : ¬ MatchReflexive := by
  intro h
  have := h asciiLower asciiLower_spec noUser _ _ _ _ _ badJuliaVersion_ctor
    (unionOrder_ok _ _ (by decide +kernel))
  rw [badJuliaVersion_match] at this
  cases this

/-! ## `platforms-compare-strategies-alias` -/

theorem juliaVersion_mk :
    mkPlatform asciiLower (s% "x86_64") (s% "linux") [(s% "julia_version", .str (s% "1.6.0"))] false [] =
      .ok (⟨[(s% "arch", s% "x86_64"), (s% "os", s% "linux"), (s% "julia_version", s% "1.6.0"),
        (s% "libc", s% "glibc")], [(s% "julia_version", .juliaMinor)]⟩, [(s% "julia_version", .juliaMinor)]) := by
  decide +kernel

theorem ctorKeepsStrategies_refuted : ¬ CtorKeepsStrategies := by
  intro h
  have := h asciiLower asciiLower_spec _ _ _ _ _ _ _ juliaVersion_mk
  cases this

/-! ## `platforms-select-order` -/

def gfortranKey (minor : Char) : Platform :=
  ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "linux"), (s% "libgfortran_version", ['5', '.', minor, '.', '0']),
    (s% "libc", s% "glibc")], []⟩

def linuxHost : Platform := ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "linux"), (s% "libc", s% "glibc")], []⟩

theorem gfortranKey_ctor (minor : Char) (h : minor = '0' ∨ minor = '5') :
    platform asciiLower (s% "x86_64") (s% "linux") [(s% "libgfortran_version", .str ['5', '.', minor, '.', '0'])] true =
      .ok (gfortranKey minor) := by
  rcases h with rfl | rfl <;> decide +kernel

def hostOrder (p : Platform) : List Str := unionOrder p linuxHost

def gfortranEntries : List (Platform × Str) := [(gfortranKey '0', s% "5.0"), (gfortranKey '5', s% "5.5")]

theorem select_forward :
    selectPlatform (fun _ _ _ _ _ => .ok true) hostOrder gfortranEntries linuxHost = .ok (some (s% "5.0")) := by
  decide +kernel

theorem select_backward :
    selectPlatform (fun _ _ _ _ _ => .ok true) hostOrder gfortranEntries.reverse linuxHost = .ok (some (s% "5.5")) := by
  decide +kernel

theorem selectOrderIndependent_refuted : ¬ SelectOrderIndependent := by
  intro h
  have := h (fun _ _ _ _ _ => .ok true) hostOrder gfortranEntries gfortranEntries.reverse linuxHost
    (List.reverse_perm _).symm (by decide +kernel) (by
      intro e he
      simp only [gfortranEntries, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact unionOrder_ok _ _ (by decide +kernel))
  rw [select_forward, select_backward] at this
  cases this

/-! ## `platforms-dl-name-four-part` -/

theorem cublas_parse :
    parseDlNameVersion (s% "libcublas" ++ s% ".so" ++ [s% "12", s% "1", s% "3", s% "1"].flatMap ('.' :: ·)) (s% "linux") =
      .error (.argumentError "invalid version string") := by decide +kernel

theorem dlNameNoThrow_refuted : ¬ DlNameNoThrow := by
  intro h
  obtain ⟨r, hr⟩ := h (s% "libcublas") [s% "12", s% "1", s% "3", s% "1"] (by decide) (by decide) (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> decide)
  rw [cublas_parse] at hr
  cases hr

/-! ## `platforms-detect-libstdcxx-csl` -/

/-- A process in which `CompilerSupportLibraries_jll` is loaded and the loaded
libstdc++ exports every `GLIBCXX_3.4.m`. -/
def cslProc : Proc := ⟨true, [s% "/opt/julia/lib/julia/libstdc++.so.6"], fun _ => true⟩

theorem cslProc_detect : detectLibstdcxxVersion cslProc 30 = .ok none := by decide +kernel

theorem detectLibstdcxx_refuted : ¬ DetectLibstdcxx := by
  intro h
  obtain ⟨v, hv⟩ := h cslProc 30 30 _ (List.mem_singleton.mpr rfl) (by decide +kernel) (by decide) (by decide) rfl
  rw [cslProc_detect] at hv
  cases hv

end JuliaLean.Platforms
