import JuliaLean.RuntimeCov.Common

/-!
`base/options.jl`: the `JLOptions` record mirrored from `jl_options`, the
color decision, its `show` method, the command-table reader, and the
coverage-tracking query.
-/

namespace JuliaLean.RuntimeCov.Options

open JuliaLean.RuntimeCov

/-- `JLOptions()`, base/options.jl:85: one `unsafe_load` of the runtime's
`jl_options` global, modelled as returning the runtime record unchanged. -/
def jlOptions {α : Type} (runtimeRecord : α) : α := runtimeRecord

/-- `colored_text(opts)`, base/options.jl:93-103, with the `color` field and
the environment lookup as inputs. `none` is Julia's `nothing`. -/
def coloredText (color : Int) (env : String → Option String) : Option Bool :=
  if color != 0 then some (color == 1)
  else if !((env "FORCE_COLOR").getD "").isEmpty then some true
  else if !((env "NO_COLOR").getD "").isEmpty then some false
  else none

/-- A field value as `show(::IO, ::JLOptions)` sees it. -/
inductive FieldValue where
  /-- A `Ptr{UInt8}`: `none` is `C_NULL`. -/
  | cstr (s : Option String)
  /-- A `Ptr{Ptr{UInt8}}` command table: printed via `unsafe_load_commands`. -/
  | cmds (reprOfCommands : String)
  /-- Any other field: printed with `repr`. -/
  | other (reprText : String)

/-- The printed value of one field, base/options.jl:110-115. -/
def fieldText : FieldValue → String
  | .cstr none => "\"\""
  | .cstr (some s) => "\"" ++ s ++ "\""
  | .cmds r => r
  | .other r => r

/-- The body of the loop at base/options.jl:109-117: field `i` (1-based) prints
`name = value`, then the separator `", "` when `i < nfields` (the flag). -/
def showFields (nfields : Nat) : Nat → List (String × FieldValue) → List (String × Bool)
  | _, [] => []
  | i, (f, v) :: rest =>
    (f ++ " = " ++ fieldText v, decide (i < nfields)) :: showFields nfields (i + 1) rest

/-- `show(io, opt::JLOptions)`, base/options.jl:105-119, as the printed text. -/
def showOptions (fields : List (String × FieldValue)) : String :=
  "JLOptions(" ++ String.join ((showFields fields.length 1 fields).map
    (fun p => p.1 ++ (if p.2 then ", " else ""))) ++ ")"

/-- The command table read by `unsafe_load_commands`: successive
`Ptr{UInt8}` slots, `none` for `C_NULL`; a present slot holds its first byte as
a `Char` and the rest of the C string. -/
def loadCommandsFrom : List (Option (Char × String)) → List (Char × String)
  | [] => []
  | none :: _ => []
  | some e :: rest => e :: loadCommandsFrom rest

/-- `unsafe_load_commands(v)`, base/options.jl:121-133: `none` is a null table
pointer. -/
def unsafeLoadCommands (v : Option (List (Option (Char × String)))) : List (Char × String) :=
  match v with
  | none => []
  | some table => loadCommandsFrom table

/-- `is_file_tracked(file)`, base/options.jl:135-137. -/
def isFileTracked (runtime : Sym → Int) (file : Sym) : Bool := runtime file == 1

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
