import JuliaLean.Proofs.stdlib.Markdown.src.Support

namespace JuliaLean.Markdown

def HashheaderTotal : Prop :=
  ∀ (α : Type) (inl : Bytes → α) (s : Bytes),
    throwsJl (runOn (hashheader (fun b => .ok (inl b))) s) = false

/-- `github_paragraph` throws no exception on any input, given a breaking-block parser and an
inline parser that do not throw. -/

def ListNoOverflow : Prop :=
  ∀ (doc : Bytes → Unit) (s : Bytes),
    errIs .overflowError (runOn (listP (fun b => .ok (doc b))) s) = false

/-- `list` throws no `ArgumentError` on any input, given a nested parser that does not throw. -/
def ListNoArgumentError : Prop :=
  ∀ (doc : Bytes → Unit) (s : Bytes),
    errIs .argumentError (runOn (listP (fun b => .ok (doc b))) s) = false

/-! ## Tight and loose lists -/

/-- The `loose` flag of a list that `list` parses from `s` (`false` if it declines or throws). -/

def ListTrailingBlankTight : Prop :=
  ∀ (xs : List Bytes) (t : Bytes), xs ≠ [] → (∀ x ∈ xs, isLetters x = true) → isLetters t = true →
    listLoose (xs.flatMap (fun x => bytes% "- " ++ x ++ [10]) ++ [10] ++ t) = false

/- `plain` prints a loose list of one-word paragraphs so that `list` reads it back loose. -/

end JuliaLean.Markdown
