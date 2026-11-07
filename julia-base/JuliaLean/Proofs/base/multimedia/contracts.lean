import JuliaLean.base.multimedia


namespace JuliaLean.ErrorShow


def MimeConstructionAndPrinting : Prop := ∀ text : String,
  makeMime text = text ∧ printMime (makeMime text) = text ∧
    showMime (makeMime text) = "MIME type " ++ text

def ShowableAndDisplayable : Prop :=
  (∀ hasShowMethod : Bool, showable hasShowMethod = hasShowMethod) ∧
  (∀ stack : List DisplayBackend, ∀ mime : Mime,
    displayable stack mime = stack.any (fun backend => backend.supported.contains mime)) ∧
  (∀ stack : List DisplayBackend, ∀ mime : Mime,
    topDisplay stack mime = stack.reverse.find? (fun backend => backend.supported.contains mime))

theorem mimeConstructionAndPrinting_proven : MimeConstructionAndPrinting := by
  intro text
  simp [makeMime, printMime, showMime]

theorem showableAndDisplayable_proven : ShowableAndDisplayable := by
  constructor
  · intro hasShowMethod
    rfl
  constructor
  · intro stack mime
    rfl
  · intro stack mime
    rfl

end JuliaLean.ErrorShow
