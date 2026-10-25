import JuliaLean.Platforms.Parse
import JuliaLean.Platforms.Match
import JuliaLean.Platforms.DlName
import JuliaLean.Platforms.Detect

/-!
# Properties of `base/binaryplatforms.jl`
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber vprint veq)

/-! ## Round trips and validation -/

/-- `parse(Platform, triplet(p)) == p` for every platform the constructor
accepts with `validate_strict = true`. -/
def TripletRoundtrip : Prop :=
  ∀ lc, LcSpec lc → ∀ (a o : Str) (ts : List (Str × TagVal)) (p : Platform),
    platform lc a o ts true = .ok p →
    ∃ t q, triplet p = .ok t ∧ parsePlatform lc false t = .ok q ∧ peq p q = true

/-- `parse(Platform, triplet(p)) == p` for every platform `p` that `parse` returns. -/
def ParseTripletParse : Prop :=
  ∀ lc, LcSpec lc → ∀ (s : Str) (p : Platform), parsePlatform lc false s = .ok p →
    ∃ t q, triplet p = .ok t ∧ parsePlatform lc false t = .ok q ∧ peq p q = true

/-- `parse(Platform, triplet(p)) == p` for every platform accepted with
`validate_strict = true` from an architecture, an OS and optional `libc` and
`call_abi` values: every architecture/OS/libc/call ABI combination. -/
def CoreTripletRoundtrip : Prop :=
  ∀ lc, LcSpec lc → ∀ (a o : Str) (libcv cav : Option Str) (p : Platform),
    platform lc a o ((libcv.map fun v => (s% "libc", TagVal.str v)).toList ++
      (cav.map fun v => (s% "call_abi", TagVal.str v)).toList) true = .ok p →
    ∃ t q, triplet p = .ok t ∧ parsePlatform lc false t = .ok q ∧ peq p q = true

/-- `triplet(p)` returns for every platform accepted with `validate_strict = true`. -/
def StrictTripletTotal : Prop :=
  ∀ lc, LcSpec lc → ∀ (a o : Str) (ts : List (Str × TagVal)) (p : Platform),
    platform lc a o ts true = .ok p → ∃ t, triplet p = .ok t

/-- The constructor leaves the caller's `compare_strategies` dictionary unchanged. -/
def CtorKeepsStrategies : Prop :=
  ∀ lc, LcSpec lc → ∀ (a o : Str) (ts : List (Str × TagVal)) (vs : Bool) (cs : Dict Strat) (p : Platform)
    (cs' : Dict Strat), mkPlatform lc a o ts vs cs = .ok (p, cs') → cs' = cs

/-- `add_tag!` throws exactly when the tag name or the lowercased value contains
one of the characters `+- /<>:"'\|?*`. -/
def AddTagRejectsNonos : Prop :=
  ∀ lc, LcSpec lc → ∀ (tags : Tags) (tag value : Str),
    (∃ r, addTag lc tags tag value = .ok r) ↔ (tag.all (!isNono ·) = true ∧ value.all (!isNono ·) = true)

/-- Without extra tags, `arch` is normalised, `os` lowercased, `libc` defaults to
`glibc` on Linux and `msvcrt` on Windows (and is absent elsewhere), and
`call_abi` defaults to `eabihf` on 32-bit ARM Linux (and is absent elsewhere). -/
def ConstructorDefaults : Prop :=
  ∀ lc, LcSpec lc → ∀ (a o : Str) (p : Platform), platform lc a o [] false = .ok p →
    arch p = some (normalizeArch lc a) ∧ os p = some (lower lc o) ∧
    libc p = (if lower lc o == s% "linux" then some (s% "glibc")
      else if lower lc o == s% "windows" then some (s% "msvcrt") else none) ∧
    callAbi p = (if lower lc o == s% "linux" && [s% "armv7l", s% "armv6l"].contains (normalizeArch lc a)
      then some (s% "eabihf") else none)

/-! ## `platforms_match` -/

/-- `platforms_match(p, p)` is `true` for every platform accepted with
`validate_strict = true`. -/
def MatchReflexive : Prop :=
  ∀ lc, LcSpec lc → ∀ (usem : UserSem) (a o : Str) (ts : List (Str × TagVal)) (p : Platform) (order : List Str),
    platform lc a o ts true = .ok p → IsUnionOrder order p p → platformsMatch usem order p p = .ok true

/-- `platforms_match(a, b) == platforms_match(b, a)` whenever both return, for
platforms using the comparison strategies of `base/binaryplatforms.jl`. -/
def MatchSymmetric : Prop :=
  ∀ (usem : UserSem) (a b : Platform) (order order' : List Str) (x y : Bool),
    BuiltinStrats a → BuiltinStrats b → IsUnionOrder order a b → IsUnionOrder order' b a →
    platformsMatch usem order a b = .ok x → platformsMatch usem order' b a = .ok y → x = y

/-- The result of `platforms_match` does not depend on the iteration order of the
key `Set` (whenever it returns). -/
def MatchOrderIndependent : Prop :=
  ∀ (usem : UserSem) (a b : Platform) (order order' : List Str) (x y : Bool),
    IsUnionOrder order a b → IsUnionOrder order' a b →
    platformsMatch usem order a b = .ok x → platformsMatch usem order' a b = .ok y → x = y

/-- `platforms_match(a, b)` is `true` exactly when every key both platforms
have matches under the selected comparison strategy and the `sanitize` tag is
present in both or in neither (keys present in only one are ignored otherwise). -/
def MatchSemantics : Prop :=
  ∀ (usem : UserSem) (a b : Platform) (order : List Str), IsUnionOrder order a b →
    (platformsMatch usem order a b = .ok true ↔
      ((∀ k, haskey a.tags k = true → haskey b.tags k = true → matchKey usem a b k = .ok true) ∧
        haskey a.tags (s% "sanitize") = haskey b.tags (s% "sanitize")))

/-- `platforms_match` never returns `true` when `a` and `b` set two different
non-default comparison strategies for a key both have. -/
def MatchConflictingStrategies : Prop :=
  ∀ (usem : UserSem) (a b : Platform) (order : List Str) (k : Str), IsUnionOrder order a b →
    haskey a.tags k = true → haskey b.tags k = true → strategy a k ≠ .dflt → strategy b k ≠ .dflt →
    strategy a k ≠ strategy b k → platformsMatch usem order a b ≠ .ok true

/-- `compare_version_cap` treats the requesting side's version as an upper bound
(two caps: equality), and the default `julia_version` strategy compares only
major and minor versions. -/
def StrategySemantics : Prop :=
  ∀ (usem : UserSem) (a b : Str) (va vb : VersionNumber),
    VersionNumbers.parse a = .ok va → VersionNumbers.parse b = .ok vb →
    compare usem .cap a b true false = .ok (vle vb va) ∧ compare usem .cap a b false true = .ok (vle va vb) ∧
    compare usem .cap a b true true = .ok (veq va vb) ∧
    (∀ x y, compare usem .juliaMinor a b x y = .ok (va.major == vb.major && va.minor == vb.minor))

/-! ## `select_platform` -/

/-- `select_platform` returns `nothing` only when no key matches, and otherwise
the value of a matching key with the smallest `match_loss`, whose triplet is
the lexicographically largest among the matching keys with that loss. -/
def SelectBest : Prop :=
  ∀ (usem : UserSem) (order : Platform → List Str) (es : List (Platform × Str)) (host : Platform)
    (r : Option Str), selectPlatform usem order es host = .ok r →
    match r with
    | none => ∀ e ∈ es, platformsMatch usem (order e.1) e.1 host = .ok false
    | some v => ∃ p, (p, v) ∈ es ∧ platformsMatch usem (order p) p host = .ok true ∧
        ∀ q ∈ es, platformsMatch usem (order q.1) q.1 host = .ok true →
          matchLoss p host ≤ matchLoss q.1 host ∧
          (matchLoss q.1 host = matchLoss p host → ∀ tp tq, triplet p = .ok tp → triplet q.1 = .ok tq →
            strLt tp tq = false)

/-- `select_platform` gives the same result for two `Dict`s with the same
entries, whatever their iteration orders. -/
def SelectOrderIndependent : Prop :=
  ∀ (usem : UserSem) (order : Platform → List Str) (es es' : List (Platform × Str)) (host : Platform),
    es.Perm es' → (es.map (·.1)).Pairwise (fun p q => peq p q = false) →
    (∀ e ∈ es, IsUnionOrder (order e.1) e.1 host) →
    selectPlatform usem order es host = selectPlatform usem order es' host

/-! ## `parse_dl_name_version` -/

/-- The file name of library `name` (version `v`, if any) with extension `ext`
on `os`: `name.ext.v` on Linux and the BSDs, `name.v.ext` on macOS, `name-v.ext`
on Windows (the forms in the docstring and comments,
`base/binaryplatforms.jl:868-907`). -/
def dlFileName (os name : Str) (v : Option VersionNumber) (ext : Str) : Str :=
  let vs := fun (sep : Char) => (v.map (sep :: vprint ·)).getD []
  if os == s% "windows" then name ++ vs '-' ++ '.' :: ext
  else if os == s% "macos" then name ++ vs '.' ++ '.' :: ext
  else name ++ '.' :: ext ++ vs '.'

/-- `x` is nonempty and consists of ASCII digits. -/
abbrev AllDigits (x : Str) : Prop := x ≠ [] ∧ x.all isAsciiDigit = true

/-- A trailing tag `[A-Za-z][\w\-]*` (`dash`) or `[A-Za-z][\w\.]*`. -/
def IsTag (dash : Bool) (x : Str) : Prop :=
  ∃ c r, x = c :: r ∧ isAsciiAlpha c = true ∧ r.all (fun d => isWord d || d == (if dash then '-' else '.')) = true

/-- Names whose file names the scheme cannot tell apart from a versioned one:
on macOS a name ending in `.<digits>` (versioned) or `.<digits>` plus a tag
(unversioned); on Windows (unversioned) a name ending in `-`, `-<digits/dots>`
or `-<digits/dots><tag>`. -/
def AmbiguousName (os name : Str) (versioned : Bool) : Prop :=
  if os == s% "macos" then
    ∃ pre ds t, name = pre ++ '.' :: ds ++ t ∧ AllDigits ds ∧ (t = [] ∨ (versioned = false ∧ IsTag true t))
  else if os == s% "windows" then
    versioned = false ∧ ∃ pre r, name = pre ++ '-' :: r ∧
      (r = [] ∨ ∃ ds t, r = ds ++ t ∧ ds ≠ [] ∧ ds.all (fun c => c == '.' || isAsciiDigit c) = true ∧ (t = [] ∨ IsTag false t))
  else False

/-- `parse_dl_name_version` recovers the name and version from the file name
built with `platform_dlext(p)`, for every name without `/` that the scheme
does not make ambiguous and every version without prerelease or build part. -/
def DlNameInverse : Prop :=
  ∀ (p : Platform) (o name : Str) (v : Option VersionNumber), os p = some o → '/' ∉ name →
    (∀ w, v = some w → w.pre = [] ∧ w.build = []) → ¬ AmbiguousName o name v.isSome →
    parseDlNameVersion (dlFileName o name v (platformDlext p)) o = .ok (name, v)

/-- `parse_dl_name_version` returns (does not throw) for every Linux library
name `name.so.N1.N2...` with numeric soversion components below `2^32`. -/
def DlNameNoThrow : Prop :=
  ∀ (name : Str) (comps : List Str), '/' ∉ name → comps ≠ [] →
    (∀ c ∈ comps, AllDigits c ∧ VersionNumbers.digitsValue c < 2 ^ 32) →
    ∃ r, parseDlNameVersion (name ++ s% ".so" ++ comps.flatMap ('.' :: ·)) (s% "linux") = .ok r

/-! ## `detect_libstdcxx_version` -/

/-- When a loaded libstdc++ exports `GLIBCXX_3.4.m` for some `18 ≤ m ≤
max_minor_version`, `detect_libstdcxx_version(max_minor_version)` returns a
version. -/
def DetectLibstdcxx : Prop :=
  ∀ (p : Proc) (maxMinor m : Nat) (path : Str), path ∈ p.dllist → occursIn (s% "libstdc++") path = true →
    18 ≤ m → m ≤ maxMinor → p.glibcxx m = true → ∃ v, detectLibstdcxxVersion p maxMinor = .ok (some v)

end JuliaLean.Platforms
