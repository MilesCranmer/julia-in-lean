import JuliaLean.Platforms.Lemmas
import JuliaLean.Platforms.CoreRoundtripCases

/-!
# `parse(Platform, triplet(p)) == p` for the core tags

`CoreTripletRoundtrip` holds. With `validate_strict = true` the constructor
accepts finitely many combinations of normalised architecture, lowercased OS,
`libc` and `call_abi` (`core_members`), and for each of them the round trip was
evaluated by the kernel with `asciiLower` (`core_cases`). The parse of the
resulting triplets lowercases only ASCII strings, on which every mapping
satisfying `LcSpec` agrees with `asciiLower` (`parse_congr`).
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (matchRe capture)

/-! ## `Except` steps -/

theorem jl_pure {α : Type} (x : α) : (pure x : Jl α) = .ok x := rfl
theorem jl_throw {α : Type} (e : JlError) : (throw e : Jl α) = .error e := rfl
theorem jl_bind_ok {α β : Type} (x : α) (f : α → Jl β) : ((.ok x : Jl α) >>= f) = f x := rfl
theorem jl_bind_error {α β : Type} (e : JlError) (f : α → Jl β) : ((.error e : Jl α) >>= f) = .error e := rfl

theorem bind_ok_inv {α β : Type} {x : Jl α} {f : α → Jl β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## `parsePlatform` is `parseArgs` followed by the constructor -/

theorem parse_split (lc : Char → Char) (vs : Bool) (t : Str) :
    parsePlatform lc vs t = parseArgs t >>= fun r => platform lc r.1 r.2.1 r.2.2 vs := by
  unfold parsePlatform parseArgs
  cases matchRe tripletRe t with
  | none => rfl
  | some m =>
    dsimp only
    cases getField m archMapping with
    | error => rfl
    | ok archF =>
    cases getField m osMapping with
    | error => rfl
    | ok osF =>
    cases archF with
    | ver _ => rfl
    | none => rfl
    | key a =>
    cases osF with
    | ver _ => rfl
    | none => rfl
    | key o =>
    dsimp only [jl_bind_ok, jl_pure]
    cases getField m libcMapping <;> try rfl
    cases getField m callAbiMapping <;> try rfl
    cases getField m libgfortranMapping <;> try rfl
    cases getField m libstdcxxMapping <;> try rfl
    cases getField m cxxstringMapping <;> try rfl
    cases splitTags ((capture m tagsGroup).getD []) <;> try rfl
    cases extractOsVersion ((capture m 10).getD []) (s% "darwin") <;>
      cases extractOsVersion ((capture m 13).getD []) (s% "freebsd") <;>
      cases extractOsVersion ((capture m 11).getD []) (s% "openbsd") <;>
      cases (o == s% "macos") <;> cases (o == s% "freebsd") <;> cases (o == s% "openbsd") <;> rfl

/-! ## The constructor's tag loop -/

theorem lower_congr {lc lc' : Char → Char} (H : ∀ c : Char, c.toNat < 128 → lc c = lc' c) {s : Str}
    (h : asc s = true) : lower lc s = lower lc' s := by
  unfold lower
  apply List.map_congr_left
  intro c hc
  exact H c (by simpa [asc] using List.all_eq_true.1 h c hc)

theorem addTag_congr {lc lc' : Char → Char} (H : ∀ c : Char, c.toNat < 128 → lc c = lc' c)
    (t : Tags) (k s : Str) (hs : asc s = true) : addTag lc t k s = addTag lc' t k s := by
  simp only [addTag, lower_congr H hs]

theorem addTag_ok {lc : Char → Char} {t : Tags} {k v : Str} {tags : Tags} (h : addTag lc t k v = .ok tags) :
    tags = dset t k (lower lc v) := by
  delta addTag at h
  revert h
  cases h1 : k.any isNono <;> cases h2 : (lower lc v).any isNono <;>
    simp [h2, jl_pure, jl_throw, jl_bind_error] <;> intro h <;> exact h.symm

theorem addPlatformTag_str (lc : Char → Char) (t : Tags) (k s : Str)
    (hp : plainTag (lower lc k) = true) : addPlatformTag lc t k (.str s) = addTag lc t (lower lc k) s := by
  simp only [plainTag, Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  delta addPlatformTag
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, jl_pure, jl_bind_ok, tagString]

theorem addAll_str (lc : Char → Char) (t : Tags) (k s : Str) (rest : List (Str × TagVal))
    (hao : (lower lc k == s% "arch" || lower lc k == s% "os") = false)
    (hp : plainTag (lower lc (lower lc k)) = true) :
    addAll lc t ((k, .str s) :: rest) = addTag lc t (lower lc (lower lc k)) s >>= fun t' => addAll lc t' rest := by
  rw [addAll]
  simp only [hao, Bool.false_eq_true, ↓reduceIte, addPlatformTag_str lc t _ s hp]
  all_goals intro h; cases h

theorem addAll_congr {lc lc' : Char → Char} (H : ∀ c : Char, c.toNat < 128 → lc c = lc' c) :
    ∀ (ts : List (Str × TagVal)) (t : Tags), ts.all (safeEntry lc') = true → addAll lc t ts = addAll lc' t ts
  | [], _, _ => rfl
  | (k, v) :: rest, t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨he, hr⟩ := h
    have ih : ∀ t, addAll lc t rest = addAll lc' t rest := fun t => addAll_congr H rest t hr
    cases v with
    | none =>
      have hk : asc k = true := he
      simp only [addAll, lower_congr H hk, ih]
    | str s =>
      simp only [safeEntry, Bool.and_eq_true] at he
      obtain ⟨⟨⟨hk, hk2⟩, hp⟩, hs⟩ := he
      have hL : ∀ t, addPlatformTag lc t (lower lc' k) (.str s) = addTag lc' t (lower lc' (lower lc' k)) s :=
        fun t => by
          rw [addPlatformTag_str lc t _ s (by rw [lower_congr H hk2]; exact hp), lower_congr H hk2,
            addTag_congr H _ _ _ hs]
      have hR : ∀ t, addPlatformTag lc' t (lower lc' k) (.str s) = addTag lc' t (lower lc' (lower lc' k)) s :=
        fun t => addPlatformTag_str lc' t _ s hp
      simp only [addAll, lower_congr H hk, hL, hR, ih]
    | ver _ => cases he

theorem platform_congr {lc lc' : Char → Char} (H : ∀ c : Char, c.toNat < 128 → lc c = lc' c)
    (a o : Str) (ts : List (Str × TagVal)) (vs : Bool) (ha : asc a = true) (ho : asc o = true)
    (hts : ts.all (safeEntry lc') = true) : platform lc a o ts vs = platform lc' a o ts vs := by
  have hn : normalizeArch lc a = normalizeArch lc' a := by
    simp only [normalizeArch, lower_congr H ha]
  have hA : ∀ t, addAll lc t ts = addAll lc' t ts := fun t => addAll_congr H ts t hts
  simp only [platform, mkPlatform, hn, lower_congr H ho, hA]

/-- `parse` does not depend on the lowercase mapping beyond ASCII when it hands
the constructor ASCII strings only. -/
theorem parse_congr {lc lc' : Char → Char} (H : ∀ c : Char, c.toNat < 128 → lc c = lc' c)
    (vs : Bool) (t a o : Str) (D : List (Str × TagVal)) (hargs : parseArgs t = .ok (a, o, D))
    (ha : asc a = true) (ho : asc o = true) (hD : D.all (safeEntry lc') = true) :
    parsePlatform lc vs t = parsePlatform lc' vs t := by
  rw [parse_split, parse_split, hargs]
  exact platform_congr H a o D vs ha ho hD

theorem roundtripB_sound {lc : Char → Char} (hlc : LcSpec lc) (p : Platform) (h : roundtripB p = true) :
    ∃ t q, triplet p = .ok t ∧ parsePlatform lc false t = .ok q ∧ peq p q = true := by
  unfold roundtripB at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h
    · rename_i a o D hargs
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨ha, ho⟩, hD⟩, hq⟩ := h
      split at hq
      · rename_i q hpl
        refine ⟨t, q, ht, ?_, hq⟩
        rw [parse_congr hlc.1 false t a o D hargs ha ho hD, parse_split, hargs]
        exact hpl
      · cases hq

/-! ## The constructor with `validate_strict = true` -/

theorem platform_strict_ok {lc : Char → Char} {a o : Str} {ts : List (Str × TagVal)} {p : Platform}
    (h : platform lc a o ts true = .ok p) :
    ∃ tags, addAll lc [(s% "arch", normalizeArch lc a), (s% "os", lower lc o)] ts = .ok tags ∧
      validateTags (finTags (normalizeArch lc a) (lower lc o) tags) = .ok () ∧
      p = ⟨finTags (normalizeArch lc a) (lower lc o) tags,
        ctorStrats (finTags (normalizeArch lc a) (lower lc o) tags)⟩ := by
  cases h1 : addAll lc [(s% "arch", normalizeArch lc a), (s% "os", lower lc o)] ts with
  | error e =>
    have : platform lc a o ts true = .error e := by
      dsimp only [platform, mkPlatform]
      rw [h1]
      rfl
    rw [this] at h
    cases h
  | ok tags =>
    cases h2 : validateTags (finTags (normalizeArch lc a) (lower lc o) tags) with
    | error e =>
      have : platform lc a o ts true = .error e := by
        dsimp only [platform, mkPlatform]
        rw [h1]
        show Except.map _ (Except.bind (validateTags (finTags (normalizeArch lc a) (lower lc o) tags)) _) = _
        rw [h2]
        rfl
      rw [this] at h
      cases h
    | ok u =>
      have : platform lc a o ts true = .ok ⟨finTags (normalizeArch lc a) (lower lc o) tags,
          ctorStrats (finTags (normalizeArch lc a) (lower lc o) tags)⟩ := by
        dsimp only [platform, mkPlatform]
        rw [h1]
        show Except.map _ (Except.bind (validateTags (finTags (normalizeArch lc a) (lower lc o) tags)) _) = _
        rw [h2]
        rfl
      rw [this] at h
      cases h
      exact ⟨tags, rfl, h2, rfl⟩

theorem lower_fixed {lc : Char → Char} (hlc : LcSpec lc) {s : Str} (h : asc s = true)
    (hs : lower asciiLower s = s) : lower lc s = s :=
  (lower_congr hlc.1 h).trans hs

/-- The tag loop on the optional `libc` and `call_abi` arguments. -/
theorem addAll_core {lc : Char → Char} (hlc : LcSpec lc) {t : Tags} {lv cv : Option Str} {tags : Tags}
    (h : addAll lc t ((lv.map fun v => (s% "libc", TagVal.str v)).toList ++
      (cv.map fun v => (s% "call_abi", TagVal.str v)).toList) = .ok tags) :
    tags = setOpt (setOpt t (s% "libc") (lv.map (lower lc))) (s% "call_abi") (cv.map (lower lc)) := by
  have hl : lower lc (s% "libc") = s% "libc" := lower_fixed hlc (by decide) (by decide)
  have hc : lower lc (s% "call_abi") = s% "call_abi" := lower_fixed hlc (by decide) (by decide)
  have aoL : (lower lc (s% "libc") == s% "arch" || lower lc (s% "libc") == s% "os") = false := by
    rw [hl]; decide
  have aoC : (lower lc (s% "call_abi") == s% "arch" || lower lc (s% "call_abi") == s% "os") = false := by
    rw [hc]; decide
  have pL : plainTag (lower lc (lower lc (s% "libc"))) = true := by rw [hl, hl]; decide
  have pC : plainTag (lower lc (lower lc (s% "call_abi"))) = true := by rw [hc, hc]; decide
  have stepC : ∀ (t : Tags) (w : Str) (tags : Tags),
      addAll lc t [(s% "call_abi", .str w)] = .ok tags → tags = dset t (s% "call_abi") (lower lc w) := by
    intro t w tags h
    rw [addAll_str lc t _ w [] aoC pC, hc, hc] at h
    obtain ⟨t1, h1, h2⟩ := bind_ok_inv h
    rw [addTag_ok h1] at h2
    exact (Except.ok.inj h2).symm
  cases lv with
  | none =>
    cases cv with
    | none => exact (Except.ok.inj h).symm
    | some w => exact stepC t w tags h
  | some v =>
    simp only [Option.map_some, Option.toList_some, List.cons_append, List.nil_append] at h
    rw [addAll_str lc t _ v _ aoL pL, hl, hl] at h
    obtain ⟨t1, h1, h2⟩ := bind_ok_inv h
    rw [addTag_ok h1] at h2
    cases cv with
    | none => exact (Except.ok.inj h2).symm
    | some w => exact stepC _ w tags h2

/-! ## `dget` on the constructed tags -/

theorem dget_dset_ne (t : Tags) (k k' v : Str) (h : k ≠ k') : dget (dset t k v) k' = dget t k' := by
  unfold dset dget
  split
  · rw [List.find?_map]
    have hf : ((fun p : Str × Str => p.1 == k') ∘ fun p => if p.1 == k then (k, v) else p) =
        fun p => p.1 == k' := by
      funext p
      simp only [Function.comp]
      split <;> simp_all
    rw [hf]
    cases hq : List.find? (fun p => p.1 == k') t with
    | none => rfl
    | some q =>
      have hq' : q.1 = k' := by simpa using List.find?_some hq
      have hqk : q.1 ≠ k := fun e => h (e.symm.trans hq')
      simp [hqk]
  · simp [List.find?_append, h]

theorem dget_dset_self (t : Tags) (k v : Str) : dget (dset t k v) k = some v := by
  unfold dset
  split
  · rename_i hk
    unfold dget
    rw [List.find?_map]
    have hf : ((fun p : Str × Str => p.1 == k) ∘ fun p => if p.1 == k then (k, v) else p) =
        fun p => p.1 == k := by
      funext p
      simp only [Function.comp]
      split <;> simp_all
    rw [hf]
    unfold haskey dget at hk
    cases hq : List.find? (fun p => p.1 == k) t with
    | none => simp [hq] at hk
    | some q =>
      have hq' := List.find?_some hq
      simp_all
  · rename_i hk
    have hn : List.find? (fun p : Str × Str => p.1 == k) t = none := by
      unfold haskey dget at hk
      cases hq : List.find? (fun p : Str × Str => p.1 == k) t with
      | none => rfl
      | some q => simp [hq] at hk
    simp [dget, List.find?_append, hn]

theorem dget_ite_ne (c : Bool) (t : Tags) (k k' v : Str) (h : k ≠ k') :
    dget (if c = true then dset t k v else t) k' = dget t k' := by
  split
  · exact dget_dset_ne t k k' v h
  · rfl

theorem haskey_ite_ne (c : Bool) (t : Tags) (k k' v : Str) (h : k ≠ k') :
    haskey (if c = true then dset t k v else t) k' = haskey t k' := by
  unfold haskey
  rw [dget_ite_ne c t k k' v h]

theorem dget_setOpt_ne (t : Tags) (k k' : Str) (L : Option Str) (h : k ≠ k') :
    dget (setOpt t k L) k' = dget t k' := by
  cases L with
  | none => rfl
  | some v => exact dget_dset_ne t k k' v h

theorem dget_core_ne (A O : Str) (L C : Option Str) (k : Str) (h1 : s% "libc" ≠ k) (h2 : s% "call_abi" ≠ k) :
    dget (coreTags A O L C) k =
      dget [(s% "arch", A), (s% "os", O)] k := by
  simp only [coreTags, finTags, dget_ite_ne _ _ _ _ _ h1, dget_ite_ne _ _ _ _ _ h2, dget_setOpt_ne _ _ _ _ h1,
    dget_setOpt_ne _ _ _ _ h2]

theorem dget_core_libc (A O X : Str) (C : Option Str) :
    dget (coreTags A O (some X) C) (s% "libc") = some X := by
  have hne : s% "call_abi" ≠ s% "libc" := by decide
  have h0 : dget (setOpt (setOpt [(s% "arch", A), (s% "os", O)] (s% "libc") (some X)) (s% "call_abi") C)
      (s% "libc") = some X := by
    rw [dget_setOpt_ne _ _ _ _ hne]
    exact dget_dset_self _ _ _
  have hk : haskey (setOpt (setOpt [(s% "arch", A), (s% "os", O)] (s% "libc") (some X)) (s% "call_abi") C)
      (s% "libc") = true := by
    unfold haskey; rw [h0]; rfl
  simp only [coreTags, finTags, hk, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    dget_ite_ne _ _ _ _ _ hne, h0]

theorem dget_core_cav (A O Y : Str) (L : Option Str) :
    dget (coreTags A O L (some Y)) (s% "call_abi") = some Y := by
  have hne : s% "libc" ≠ s% "call_abi" := by decide
  have h0 : dget (setOpt (setOpt [(s% "arch", A), (s% "os", O)] (s% "libc") L) (s% "call_abi") (some Y))
      (s% "call_abi") = some Y := dget_dset_self _ _ _
  have hk : haskey (setOpt (setOpt [(s% "arch", A), (s% "os", O)] (s% "libc") L) (s% "call_abi") (some Y))
      (s% "call_abi") = true := by
    unfold haskey; rw [h0]; rfl
  simp only [coreTags, finTags, haskey_ite_ne _ _ _ _ _ hne, hk, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, dget_ite_ne _ _ _ _ _ hne, h0]

/-! ## `validate_tags` -/

def libcOK (O : Str) (l : Option Str) : Bool :=
  if O == s% "linux" then (match l with | some v => [s% "glibc", s% "musl"].contains v | none => false)
  else if O == s% "windows" then (match l with | some v => [s% "msvcrt", s% "ucrt"].contains v | none => false)
  else l.isNone

def cavOK (A O : Str) (c : Option Str) : Bool :=
  if O == s% "linux" && [s% "armv7l", s% "armv6l"].contains A then
    (match c with | some v => [s% "eabihf", s% "eabi"].contains v | none => false)
  else c.isNone

theorem beq_windows_macos : (s% "windows" == s% "macos") = false := by decide
theorem beq_windows_linux : (s% "windows" == s% "linux") = false := by decide
theorem beq_macos_linux : (s% "macos" == s% "linux") = false := by decide

/-- Evaluate literal Boolean conditions, the `if`s on them and `Except` steps in the goal. -/
local macro "vsimp" : tactic =>
  `(tactic| simp only [Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    jl_bind_ok, jl_bind_error, reduceCtorEq, Option.isSome_some, Option.isSome_none, Option.getD_some,
    Option.getD_none, Option.isNone_none, Option.isNone_some, beq_self_eq_true, and_self, and_true, true_and,
    false_implies, implies_true, beq_windows_macos, beq_windows_linux, beq_macos_linux])

/-- What `validate_tags` checks of the architecture, OS, `libc` and `call_abi` tags,
following its branches (`base/binaryplatforms.jl:222-270`). -/
theorem validate_spec {T : Tags} {A O : Str} (h : validateTags T = .ok ())
    (ha : dget T (s% "arch") = some A) (ho : dget T (s% "os") = some O) :
    archs.contains A = true ∧ oses.contains O = true ∧
    libcOK O (dget T (s% "libc")) = true ∧ cavOK A O (dget T (s% "call_abi")) = true := by
  delta validateTags at h
  simp only [archs, oses, libcOK, cavOK]
  simp only [ha, ho, haskey, jl_pure, jl_bind_ok, jl_throw, jl_bind_error] at h
  revert h
  cases [s% "x86_64", s% "i686", s% "armv7l", s% "armv6l", s% "aarch64", s% "powerpc64le",
    s% "riscv64"].contains A <;> vsimp
  cases [s% "linux", s% "macos", s% "freebsd", s% "openbsd", s% "windows"].contains O <;> vsimp
  cases ew : (O == s% "windows")
  · cases em : (O == s% "macos")
    · cases el : (O == s% "linux")
      · vsimp
        cases dget T (s% "libc") <;>
          rcases Option.eq_none_or_eq_some (dget T (s% "call_abi")) with hw | ⟨w, hw⟩ <;> simp only [hw] <;> vsimp
      · obtain rfl : O = s% "linux" := beq_iff_eq.1 el
        vsimp
        cases dget T (s% "libc") with
        | none => vsimp
        | some v =>
          vsimp
          cases [s% "glibc", s% "musl"].contains v <;> vsimp
          cases [s% "armv7l", s% "armv6l"].contains A <;> vsimp <;>
            rcases Option.eq_none_or_eq_some (dget T (s% "call_abi")) with hw | ⟨w, hw⟩ <;> simp only [hw] <;>
              vsimp <;> cases [s% "eabihf", s% "eabi"].contains w <;> vsimp
    · obtain rfl : O = s% "macos" := beq_iff_eq.1 em
      vsimp
      cases [s% "x86_64", s% "aarch64"].contains A <;> vsimp
      cases dget T (s% "libc") <;>
        rcases Option.eq_none_or_eq_some (dget T (s% "call_abi")) with hw | ⟨w, hw⟩ <;> simp only [hw] <;> vsimp
  · obtain rfl : O = s% "windows" := beq_iff_eq.1 ew
    vsimp
    cases [s% "x86_64", s% "i686", s% "armv7l", s% "aarch64"].contains A <;> vsimp
    cases dget T (s% "libc") with
    | none => vsimp
    | some v =>
      vsimp
      cases [s% "msvcrt", s% "ucrt"].contains v <;> vsimp
      rcases Option.eq_none_or_eq_some (dget T (s% "call_abi")) with hw | ⟨w, hw⟩ <;> simp only [hw] <;> vsimp

theorem libcOK_mem {O X : Str} (h : libcOK O (some X) = true) : some X ∈ libcOpts := by
  unfold libcOK at h
  split at h
  · have hm := List.contains_iff_mem.1 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> decide
  · split at h
    · have hm := List.contains_iff_mem.1 h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> decide
    · cases h

theorem cavOK_mem {A O Y : Str} (h : cavOK A O (some Y) = true) : some Y ∈ cavOpts := by
  unfold cavOK at h
  split at h
  · have hm := List.contains_iff_mem.1 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> decide
  · cases h

/-- The combinations `validate_tags` accepts. -/
theorem core_members {A O : Str} {L C : Option Str} (h : validateTags (coreTags A O L C) = .ok ()) :
    A ∈ archs ∧ O ∈ oses ∧ L ∈ libcOpts ∧ C ∈ cavOpts := by
  have ha : dget (coreTags A O L C) (s% "arch") = some A := by
    rw [dget_core_ne _ _ _ _ _ (by decide) (by decide)]; rfl
  have ho : dget (coreTags A O L C) (s% "os") = some O := by
    rw [dget_core_ne _ _ _ _ _ (by decide) (by decide)]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := validate_spec h ha ho
  refine ⟨List.contains_iff_mem.1 h1, List.contains_iff_mem.1 h2, ?_, ?_⟩
  · cases L with
    | none => exact List.mem_cons_self
    | some X =>
      rw [dget_core_libc] at h3
      exact libcOK_mem h3
  · cases C with
    | none => exact List.mem_cons_self
    | some Y =>
      rw [dget_core_cav] at h4
      exact cavOK_mem h4

/-! ## The round trip -/

theorem coreTripletRoundtrip_proven : CoreTripletRoundtrip := by
  intro lc hlc a o lv cv p h
  obtain ⟨tags, h1, h2, rfl⟩ := platform_strict_ok h
  obtain rfl := addAll_core hlc h1
  generalize normalizeArch lc a = A at h2 ⊢
  generalize lower lc o = O at h2 ⊢
  generalize lv.map (lower lc) = L at h2 ⊢
  generalize cv.map (lower lc) = C at h2 ⊢
  change validateTags (coreTags A O L C) = .ok () at h2
  obtain ⟨hA, hO, hL, hC⟩ := core_members h2
  have hc := core_cases A hA O hO L hL C hC
  unfold checkCase at hc
  rw [h2] at hc
  exact roundtripB_sound hlc (corePlatform A O L C) hc

end JuliaLean.Platforms
