import JuliaLean.Artifacts.Props
import JuliaLean.Platforms.CoreRoundtrip
import JuliaLean.Platforms.SelectProofs

namespace JuliaLean.Artifacts

open JuliaLean

/-! ## Slash splitting -/

theorem splitSlashes_noSlash (s : Str) (h : s.all (!isSlash ·) = true) :
    splitSlashes s = [s] := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hc : isSlash c = false := by simpa using h.1
      simp [splitSlashes, hc, ih h.2]

theorem splitSlashes_append (name tail : Str) (sep : Char)
    (hn : name.all (!isSlash ·) = true) (ht : tail.all (!isSlash ·) = true)
    (hs : isSlash sep = true) :
    splitSlashes (name ++ sep :: tail) = [name, tail] := by
  induction name with
  | nil => simp [splitSlashes, hs, splitSlashes_noSlash tail ht]
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hn
      have hc : isSlash c = false := by simpa using hn.1
      simp [splitSlashes, hc, ih hn.2]

theorem slashSplitSemantics_proven : SlashSplitSemantics := by
  intro name tail hn ht
  have hbare := splitSlashes_noSlash name hn
  have hf := splitSlashes_append name tail '/' hn ht (by decide)
  have hb := splitSlashes_append name tail '\\' hn ht (by decide)
  simp [splitArtifactSlash, hbare, hf, hb, joinParts]

/-! ## Metadata -/

theorem unpackPlatformRequired_proven : UnpackPlatformRequired := by
  intro lc m h
  rcases h with hos | harch
  · simp [unpackPlatform, hos, pure, Except.pure]
  · cases hos : dget m.stringFields (s% "os") with
    | none => simp [unpackPlatform, hos, pure, Except.pure]
    | some os => simp [unpackPlatform, hos, harch, pure, Except.pure]

theorem dget_packTag_self (m : Meta) (key value : Str) :
    dget (packTag m (key, value)).stringFields key = some value := by
  simpa [packTag, dget, dset] using Platforms.dget_dset_self m.stringFields key value

theorem dget_packTag_ne (m : Meta) (setKey key value : Str) (h : setKey ≠ key) :
    dget (packTag m (setKey, value)).stringFields key = dget m.stringFields key := by
  simpa [packTag, dget, dset] using
    Platforms.dget_dset_ne m.stringFields setKey key value h

theorem packFold_preserves (tags : List (Str × Str)) (m : Meta) (key value : Str)
    (h : dget m.stringFields key = some value) :
    ∃ packedValue, dget (tags.foldl packTag m).stringFields key = some packedValue := by
  induction tags generalizing m value with
  | nil => exact ⟨value, h⟩
  | cons entry rest ih =>
      by_cases heq : entry.1 = key
      · subst key
        exact ih (packTag m entry) entry.2 (dget_packTag_self m entry.1 entry.2)
      · exact ih (packTag m entry) value ((dget_packTag_ne m entry.1 key entry.2 heq).trans h)

theorem packTags_member (tags : List (Str × Str)) (m : Meta) (key value : Str)
    (hmem : (key, value) ∈ tags) :
    ∃ packedValue, dget (tags.foldl packTag m).stringFields key = some packedValue := by
  induction tags generalizing m with
  | nil => contradiction
  | cons entry rest ih =>
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst entry
        exact packFold_preserves rest (packTag m (key, value)) key value
          (dget_packTag_self m key value)
      · exact ih (packTag m entry) hrest

theorem packPlatformTags_proven : PackPlatformTags := by
  intro m platform key value hmem
  exact packTags_member platform.tags m key value hmem

theorem artifactMetaSelectsBest_proven : ArtifactMetaSelectsBest := by
  intro usem order entries host result h
  cases result with
  | none => exact Platforms.selectBest_proven usem order entries host none h
  | some value => exact Platforms.selectBest_proven usem order entries host (some value) h

theorem artifactMetaRequiresHash_proven : ArtifactMetaRequiresHash := by
  intro m
  rcases m with ⟨fields, hash, download, lazy⟩
  cases hash <;> simp [requireHash]

theorem lazySelection_proven : LazySelection := by
  intro includeLazy resolved
  induction resolved with
  | nil => simp [selectDownloadable]
  | cons entry rest ih =>
      rcases entry with ⟨name, m⟩
      cases m with
      | none => simp [selectDownloadable, ih]
      | some current =>
          by_cases hcurrent : downloadable includeLazy current = true
          · intro selectedName selected
            rw [selectDownloadable, hcurrent]
            constructor
            · intro hselected
              rcases List.mem_cons.mp hselected with heq | hrest
              · cases heq
                exact ⟨List.mem_cons_self, hcurrent⟩
              · have htail := (ih selectedName selected).1 hrest
                exact ⟨List.mem_cons_of_mem _ htail.1, htail.2⟩
            · rintro ⟨hsource, heligible⟩
              rcases List.mem_cons.mp hsource with heq | hrest
              · cases heq
                exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ ((ih selectedName selected).2 ⟨hrest, heligible⟩)
          · have hfalse : downloadable includeLazy current = false := by
              cases h : downloadable includeLazy current <;> simp_all
            intro selectedName selected
            rw [selectDownloadable, hfalse]
            constructor
            · intro hselected
              have htail := (ih selectedName selected).1 hselected
              exact ⟨List.mem_cons_of_mem _ htail.1, htail.2⟩
            · rintro ⟨hsource, heligible⟩
              rcases List.mem_cons.mp hsource with heq | hrest
              · cases heq
                exact (hcurrent heligible).elim
              · exact (ih selectedName selected).2 ⟨hrest, heligible⟩

/-! ## Overrides and paths -/

theorem overridePrecedence_proven : OverridePrecedence := by
  constructor
  · intro hash low high
    simp [loadHashDepots, applyHashFile, applyHashEntry, nget, nset]
  · intro pkg name hash direct named
    simp [processNameOverrides, installNameHashes, nget, nset, dget, Platforms.dget]

theorem malformedOverridesReported_proven : MalformedOverridesReported := by
  intro state hash
  simp [applyHashEntry]

theorem artifactPathOverride_proven : ArtifactPathOverride := by
  intro hash path depots isDir
  cases h : isDir (.override path) <;>
    simp [artifactPaths, resolveOverride, nget, artifactExists, artifactPath, h]

end JuliaLean.Artifacts
