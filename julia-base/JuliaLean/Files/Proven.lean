import JuliaLean.Files.Props

namespace JuliaLean.Files

private theorem mkpathComponents_ok (components : List Component)
    (h : ∀ component ∈ components, Creatable component) :
    ∃ out, mkpathComponents components = .ok out ∧
      ∀ component ∈ out, DirectoryLike component := by
  induction components with
  | nil => simp [mkpathComponents]
  | cons component tail ih =>
      have hc := h component (by simp)
      have ht : ∀ c ∈ tail, Creatable c := by
        intro c hmem
        exact h c (by simp [hmem])
      obtain ⟨out, hout, hall⟩ := ih ht
      cases component with
      | missing =>
          refine ⟨.directory :: out, by simp [mkpathComponents, Component.create, hout], ?_⟩
          intro c hmem
          simp at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact hall c hmem
      | directory =>
          refine ⟨.directory :: out, by simp [mkpathComponents, Component.create, hout], ?_⟩
          intro c hmem
          simp at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact hall c hmem
      | symlinkDirectory =>
          refine ⟨.symlinkDirectory :: out,
            by simp [mkpathComponents, Component.create, hout], ?_⟩
          intro c hmem
          simp at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact hall c hmem
      | file => simp [Creatable] at hc
      | symlinkFile => simp [Creatable] at hc

private theorem mkpathComponents_error (components : List Component)
    (h : ¬(∀ component ∈ components, Creatable component)) :
    ∃ e out, mkpathComponents components = .error e out := by
  induction components with
  | nil => simp at h
  | cons component tail ih =>
      cases component with
      | missing =>
          have ht : ¬(∀ c ∈ tail, Creatable c) := by
            intro htail
            apply h
            intro c hmem
            simp at hmem
            rcases hmem with rfl | hmem
            · trivial
            · exact htail c hmem
          obtain ⟨e, out, hout⟩ := ih ht
          exact ⟨e, .directory :: out, by simp [mkpathComponents, Component.create, hout]⟩
      | directory =>
          have ht : ¬(∀ c ∈ tail, Creatable c) := by
            intro htail
            apply h
            intro c hmem
            simp at hmem
            rcases hmem with rfl | hmem
            · trivial
            · exact htail c hmem
          obtain ⟨e, out, hout⟩ := ih ht
          exact ⟨e, .directory :: out, by simp [mkpathComponents, Component.create, hout]⟩
      | symlinkDirectory =>
          have ht : ¬(∀ c ∈ tail, Creatable c) := by
            intro htail
            apply h
            intro c hmem
            simp at hmem
            rcases hmem with rfl | hmem
            · trivial
            · exact htail c hmem
          obtain ⟨e, out, hout⟩ := ih ht
          exact ⟨e, .symlinkDirectory :: out,
            by simp [mkpathComponents, Component.create, hout]⟩
      | file =>
          exact ⟨.io, .file :: tail, by simp [mkpathComponents, Component.create]⟩
      | symlinkFile =>
          exact ⟨.io, .symlinkFile :: tail, by simp [mkpathComponents, Component.create]⟩

theorem mkpathPostcondition_proven : MkpathPostcondition := by
  intro path
  constructor
  · intro h
    obtain ⟨out, hout, hall⟩ := mkpathComponents_ok path.components h
    refine ⟨{ path with components := out }, ?_, rfl, hall⟩
    simp [mkpath, hout]
  · intro h
    obtain ⟨e, out, hout⟩ := mkpathComponents_error path.components h
    exact ⟨e, { path with components := out }, by simp [mkpath, hout]⟩

theorem rmFlagsSpec_proven : RmFlagsSpec := by
  intro force recursive
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [rm]
  · simp [rm]
  · simp [rm]
  · intro children
    simp [rm]

theorem mvForceSpec_proven : MvForceSpec := by
  refine ⟨?_, rfl, ?_⟩
  · intro destination
    simp [mv]
  · intro destination h
    cases destination <;> simp_all [mv]

theorem tempnameContract_proven : TempnameContract := by
  intro parent candidates maxTries suffix cleanup
  rfl

theorem mktempContract_proven : MktempContract := by
  intro parent random cleanup
  constructor
  · simp [mktemp]
  · intro object
    simp [cleanupTemp]

theorem mktempdirContract_proven : MktempdirContract := by
  intro parent namePrefix random cleanup
  constructor
  · simp [mktempdir]
  · intro object
    simp [cleanupTemp]

private theorem mem_insertName (z x : Nat) (xs : List Nat) :
    z ∈ insertName x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil => simp [insertName]
  | cons y ys ih =>
      simp only [insertName]
      split <;> simp [ih, or_left_comm]

private theorem ordered_insertName (x : Nat) (xs : List Nat) (h : Ordered xs) :
    Ordered (insertName x xs) := by
  induction xs with
  | nil => simp [insertName, Ordered]
  | cons y ys ih =>
      rcases h with ⟨hy, hys⟩
      by_cases hxy : x ≤ y
      · rw [insertName, ite_eq_left hxy]
        simp only [Ordered]
        refine ⟨?_, hy, hys⟩
        intro z hz
        simp at hz
        rcases hz with rfl | hz
        · exact hxy
        · exact Nat.le_trans hxy (hy z hz)
      · rw [insertName, ite_eq_right hxy]
        simp only [Ordered]
        refine ⟨?_, ih hys⟩
        intro z hz
        have hz' := (mem_insertName z x ys).mp hz
        rcases hz' with rfl | hz'
        · omega
        · exact hy z hz'

private theorem ordered_sortNames (xs : List Nat) : Ordered (sortNames xs) := by
  induction xs with
  | nil => simp [sortNames, Ordered]
  | cons x xs ih =>
      exact ordered_insertName x (sortNames xs) ih

private theorem occurrences_insertName (needle x : Nat) (xs : List Nat) :
    occurrences needle (insertName x xs) =
      (if needle == x then 1 else 0) + occurrences needle xs := by
  induction xs with
  | nil => simp [insertName, occurrences]
  | cons y ys ih =>
      simp only [insertName]
      split <;>
        simp [occurrences, ih, Nat.add_left_comm]

private theorem sameNames_sortNames (xs : List Nat) : SameNames (sortNames xs) xs := by
  intro needle
  induction xs with
  | nil => simp [sortNames, occurrences]
  | cons x xs ih =>
      simp [sortNames, occurrences, occurrences_insertName, ih]

theorem readdirOptions_proven : ReaddirOptions := by
  intro dir scan join sort
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    exact ordered_sortNames scan
  · cases sort
    · intro name
      rfl
    · exact sameNames_sortNames scan

mutual
  private theorem walkTop_length (parent : List Nat) (tree : DirTree) :
      (walkTop parent tree).length = directoryCount tree := by
    cases tree with
    | node name files children =>
        simp [walkTop, directoryCount, walkTopForest_length, Nat.add_comm]

  private theorem walkTopForest_length (parent : List Nat) (forest : DirForest) :
      (walkTopForest parent forest).length = forestDirectoryCount forest := by
    cases forest with
    | nil => rfl
    | cons head tail =>
        simp [walkTopForest, forestDirectoryCount, walkTop_length,
          walkTopForest_length]
end

mutual
  private theorem walkBottom_length (parent : List Nat) (tree : DirTree) :
      (walkBottom parent tree).length = directoryCount tree := by
    cases tree with
    | node name files children =>
        simp [walkBottom, directoryCount, walkBottomForest_length, Nat.add_comm]

  private theorem walkBottomForest_length (parent : List Nat) (forest : DirForest) :
      (walkBottomForest parent forest).length = forestDirectoryCount forest := by
    cases forest with
    | nil => rfl
    | cons head tail =>
        simp [walkBottomForest, forestDirectoryCount, walkBottom_length,
          walkBottomForest_length]
end

theorem walkdirOrder_proven : WalkdirOrder := by
  intro parent tree
  simp [walkdir, walkTop_length, walkBottom_length]

theorem touchPostcondition_proven : TouchPostcondition := by
  intro now state
  simp [touch]

mutual
  private theorem chmodChild_nonlinks (mode : Nat) (entry : ModeEntry) :
      NonlinksHaveMode mode (chmodChild mode entry) := by
    cases entry with
    | file old => simp [chmodChild, NonlinksHaveMode]
    | link old => simp [chmodChild, NonlinksHaveMode]
    | directory tree =>
        simp [chmodChild, NonlinksHaveMode, chmodTree_nonlinks]

  private theorem chmodForest_nonlinks (mode : Nat) (forest : ModeForest) :
      ForestNonlinksHaveMode mode (chmodForest mode forest) := by
    cases forest with
    | nil => simp [chmodForest, ForestNonlinksHaveMode]
    | cons head tail =>
        simp [chmodForest, ForestNonlinksHaveMode, chmodChild_nonlinks,
          chmodForest_nonlinks]

  private theorem chmodTree_nonlinks (mode : Nat) (tree : ModeTree) :
      TreeNonlinksHaveMode mode (chmodTree mode true tree) := by
    cases tree with
    | directory old children =>
        simp [chmodTree, TreeNonlinksHaveMode, chmodForest_nonlinks]
end

mutual
  private theorem chmodChild_links (mode : Nat) (entry : ModeEntry) :
      LinksPreserved entry (chmodChild mode entry) := by
    cases entry with
    | file old => simp [chmodChild, LinksPreserved]
    | link old => simp [chmodChild, LinksPreserved]
    | directory tree =>
        simp [chmodChild, LinksPreserved, chmodTree_links]

  private theorem chmodForest_links (mode : Nat) (forest : ModeForest) :
      ForestLinksPreserved forest (chmodForest mode forest) := by
    cases forest with
    | nil => simp [chmodForest, ForestLinksPreserved]
    | cons head tail =>
        simp [chmodForest, ForestLinksPreserved, chmodChild_links,
          chmodForest_links]

  private theorem chmodTree_links (mode : Nat) (tree : ModeTree) :
      TreeLinksPreserved tree (chmodTree mode true tree) := by
    cases tree with
    | directory old children =>
        simp [chmodTree, TreeLinksPreserved, chmodForest_links]
end

theorem chmodRecursive_proven : ChmodRecursive := by
  intro mode tree
  refine ⟨chmodTree_nonlinks mode tree, chmodTree_links mode tree, ?_⟩
  cases tree
  rfl

theorem statModeLayout_proven : StatModeLayout := by
  intro mode size errno
  simp [filemode, isdir, islink, ispath, modeType, uperm, gperm, operm, filesize]

theorem fileOffsetSpec_proven : FileOffsetSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro file bytes hopen
    simp [unsafeWrite, hopen]
  · intro file bytes offset hopen
    simp [unsafeWrite, hopen]
  · intro file byte hopen hbyte
    simp [readByte, hopen, hbyte]
  · intro file count hopen
    let bytes := (file.data.drop file.position).take count
    refine ⟨bytes, { file with position := file.position + bytes.length }, ?_⟩
    simp [readBytes, hopen, bytes]
  · intro file position hopen
    constructor
    · simp [seek, hopen]
    · simp [bytesavailable]

end JuliaLean.Files
