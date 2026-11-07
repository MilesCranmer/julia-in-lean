import JuliaLean.base.options
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.Options

open JuliaLean.RuntimeCov

/-- Properties of `base/options.jl`: `JLOptions()` returns the runtime record;
a nonzero `color` option decides `colored_text` (1 means on); otherwise
`FORCE_COLOR` wins over `NO_COLOR` and neither gives `nothing`; `show` prints
one `name = value` chunk per field with exactly `nfields - 1` separators between
`JLOptions(` and `)`; `unsafe_load_commands` returns the slots before the first
null pointer, in order; `is_file_tracked` is the runtime's answer `== 1`. -/
def OptionsBodies : Prop :=
  (∀ (α : Type) (r : α), jlOptions r = r) ∧
  (∀ (c : Int) (env : String → Option String), c ≠ 0 → coloredText c env = some (c == 1)) ∧
  (∀ env : String → Option String, ((env "FORCE_COLOR").getD "").isEmpty = false →
      coloredText 0 env = some true) ∧
  (∀ env : String → Option String, ((env "FORCE_COLOR").getD "").isEmpty = true →
      ((env "NO_COLOR").getD "").isEmpty = true → coloredText 0 env = none) ∧
  (∀ fields : List (String × FieldValue), ∃ body : String,
      showOptions fields = "JLOptions(" ++ body ++ ")") ∧
  (∀ fields : List (String × FieldValue),
      ((showFields fields.length 1 fields).map Prod.fst) =
        fields.map (fun p => p.1 ++ " = " ++ fieldText p.2) ∧
      ((showFields fields.length 1 fields).map Prod.snd) =
        List.replicate (fields.length - 1) true ++ (if fields.isEmpty then [] else [false])) ∧
  (∀ table : List (Option (Char × String)),
      unsafeLoadCommands (some table) = (table.takeWhile Option.isSome).filterMap id) ∧
  unsafeLoadCommands none = [] ∧
  (∀ (rt : Sym → Int) (f : Sym), isFileTracked rt f = true ↔ rt f = 1)

theorem showFields_fst (n : Nat) : ∀ (i : Nat) (fs : List (String × FieldValue)),
    (showFields n i fs).map Prod.fst = fs.map (fun p => p.1 ++ " = " ++ fieldText p.2)
  | _, [] => rfl
  | i, _ :: rest => by simp [showFields, showFields_fst n (i + 1) rest]

theorem showFields_seps (n : Nat) : ∀ (fs : List (String × FieldValue)) (i : Nat),
    i + fs.length = n + 1 →
    (showFields n i fs).map Prod.snd =
      List.replicate (fs.length - 1) true ++ (if fs.isEmpty then [] else [false])
  | [], _, _ => rfl
  | [_], i, h => by
      have hn : ¬ i < n := by simp at h; omega
      simp [showFields, hn]
  | a :: b :: rest, i, h => by
      have hi : i < n := by simp at h; omega
      have ih := showFields_seps n (b :: rest) (i + 1) (by simp at h ⊢; omega)
      have e : showFields n i (a :: b :: rest) = (a.1 ++ " = " ++ fieldText a.2, true) ::
          showFields n (i + 1) (b :: rest) := by
        simp [showFields, hi]
      rw [e, List.map_cons, ih]
      simp [List.replicate_succ]

theorem loadCommandsFrom_eq : ∀ table : List (Option (Char × String)),
    loadCommandsFrom table = (table.takeWhile Option.isSome).filterMap id
  | [] => rfl
  | none :: _ => by simp [loadCommandsFrom]
  | some e :: rest => by simp [loadCommandsFrom, loadCommandsFrom_eq rest]

theorem optionsBodies_proven : OptionsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α r; rfl
  · intro c env hc; simp [coloredText, hc]
  · intro env h; simp [coloredText, h]
  · intro env h1 h2; simp [coloredText, h1, h2]
  · intro fields; exact ⟨_, rfl⟩
  · intro fields
    exact ⟨showFields_fst _ 1 fields, showFields_seps _ fields 1 (by omega)⟩
  · intro table; exact loadCommandsFrom_eq table
  · rfl
  · intro rt f; simp [isFileTracked]
end JuliaLean.RuntimeCov.Options
end
