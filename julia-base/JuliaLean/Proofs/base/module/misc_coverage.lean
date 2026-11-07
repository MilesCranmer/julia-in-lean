import JuliaLean.base.module

/-!
# `base/module.jl` (master `bbfa0ce4150`)

Modules are numbered; the environment gives each module's parent, name and globals,
and the package loader `require(at, name)`. The calls to `Core._import` and
`Core._using` are recorded in order. Path elements are syntax (`Ex`); a `Symbol`
is `.sym name`.
-/

namespace JuliaLean.MiscCov.Module

open JuliaLean.MiscCov

/-- `eval_import_path` (`base/module.jl:12-56`): an empty path is malformed; a single
absolute name is the module the loader returns (`Core` and `Base` directly); a longer
absolute path walks modules from the loaded root and returns the last name; leading
dots start at `at` and go up one parent per further dot; a non-module in the middle and
a `.` after a name are errors; a non-symbol element is a `TypeError`. -/
def ImportPathContract : Prop :=
  (∀ env at_ from_ kw, evalImportPath env at_ from_ [] kw = .error (.errorException "malformed import statement")) ∧
  (∀ env at_ kw (a : String) m, a ≠ "." → a ≠ "Core" → a ≠ "Base" → env.require at_ a = .ok (.mod m) →
    evalImportPath env at_ none [.sym a] kw = .ok (m, none)) ∧
  (∀ env at_ kw (b : String), b ≠ "." → evalImportPath env at_ none [.sym "Base", .sym b] kw = .ok (env.base, some b)) ∧
  (∀ env at_ kw (a b c : String) m m', a ≠ "." → a ≠ "Core" → a ≠ "Base" → b ≠ "." → c ≠ "." →
    env.require at_ a = .ok (.mod m) → env.getglobal m b = .ok (.mod m') →
    evalImportPath env at_ none [.sym a, .sym b, .sym c] kw = .ok (m', some c)) ∧
  (∀ env at_ kw (a b c : String) m, a ≠ "." → a ≠ "Core" → a ≠ "Base" → b ≠ "." →
    env.require at_ a = .ok (.mod m) → env.getglobal m b = .ok .other →
    evalImportPath env at_ none [.sym a, .sym b, .sym c] kw =
      .error (.errorException ("invalid " ++ kw ++ " path: \"" ++ b ++ "\" does not name a module"))) ∧
  (∀ env at_ kw (a : String), a ≠ "." → evalImportPath env at_ none [.sym ".", .sym a] kw = .ok (at_, some a)) ∧
  (∀ env at_ kw (a : String), a ≠ "." →
    evalImportPath env at_ none [.sym ".", .sym ".", .sym a] kw = .ok (env.parent at_, some a)) ∧
  (∀ env at_ kw (a : String) m, a ≠ "." → env.require at_ a = .ok (.mod m) → a ≠ "Core" → a ≠ "Base" →
    evalImportPath env at_ none [.sym a, .sym "."] kw =
      .error (.errorException ("invalid " ++ kw ++ " path: \".\" in identifier path"))) ∧
  (∀ env at_ from_ kw (x : Ex) xs, (match x with | .sym _ => false | _ => true) = true →
    evalImportPath env at_ from_ (x :: xs) kw = .error .typeError)

theorem importPathContract_proven : ImportPathContract := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro env at_ kw a m h1 h2 h3 h4
    simp [evalImportPath, next, h1, h2, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro env at_ kw b hb
    simp [evalImportPath, next, walk, hb, bind, Except.bind, pure, Except.pure]
  · intro env at_ kw a b c m m' h1 h2 h3 hb hc h4 h5
    simp [evalImportPath, next, walk, h1, h2, h3, hb, hc, h4, h5, bind, Except.bind, pure, Except.pure]
  · intro env at_ kw a b c m h1 h2 h3 hb h4 h5
    simp [evalImportPath, next, walk, h1, h2, h3, hb, h4, h5, bind, Except.bind, pure, Except.pure]
  · intro env at_ kw a ha
    simp [evalImportPath, next, walk, dotLoop, ha, bind, Except.bind, pure, Except.pure]
  · intro env at_ kw a ha
    simp [evalImportPath, next, walk, dotLoop, ha, bind, Except.bind, pure, Except.pure]
  · intro env at_ kw a m ha h4 h2 h3
    simp [evalImportPath, next, walk, ha, h2, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro env at_ from_ kw x xs hx
    cases x <;> simp_all [evalImportPath, next, bind, Except.bind]

/-- `eval_import_path_all` (`base/module.jl:58-65`) resolves the whole path to a module;
`check_macro_rename` (`:67-76`) rejects renaming a macro (a name starting with `@`) to a
non-macro and back; `_eval_import` (`:97-120`) calls `Core._import(to, m, asname, name,
imported)` for `import A.b [as c]` and `using A: b`, `Core._import(to, m, asname)` with
the module's own name (or the `as` name) for `import A`, and rejects a path that is not
a `.` or `as` expression; `_eval_using` (`:135-142`) calls `Core._using` and, for
`using A` in `Main`, also imports `A`. -/
def ImportContract : Prop :=
  (∀ env at_ args kw m, evalImportPath env at_ none args kw = .ok (m, none) → evalImportPathAll env at_ args kw = .ok m) ∧
  (∀ env at_ args kw m v m', evalImportPath env at_ none args kw = .ok (m, some v) → env.getglobal m v = .ok (.mod m') →
    evalImportPathAll env at_ args kw = .ok m') ∧
  (∀ a b kw, (c1 a = 64 ↔ c1 b = 64) → checkMacroRename a b kw = .ok ()) ∧
  (∀ a b kw, c1 a = 64 → c1 b ≠ 64 → ∃ msg, checkMacroRename a b kw = .error (.errorException msg)) ∧
  (∀ a b kw, c1 a ≠ 64 → c1 b = 64 → ∃ msg, checkMacroRename a b kw = .error (.errorException msg)) ∧
  (∀ env (imported : Bool) to args m b, b ≠ "" → c1 b ≠ 64 → evalImportPath env to none args (if imported then "import" else "using") = .ok (m, some b) →
    evalImport env imported to none [.expr "." args] = .ok [.imp to m b (some b) imported]) ∧
  (∀ env (imported : Bool) to args m b c, c1 b ≠ 64 → c1 c ≠ 64 →
    evalImportPath env to none args (if imported then "import" else "using") = .ok (m, some b) →
    evalImport env imported to none [.expr "as" [.expr "." args, .sym c]] = .ok [.imp to m c (some b) imported]) ∧
  (∀ env (imported : Bool) to args m, evalImportPath env to none args (if imported then "import" else "using") = .ok (m, none) →
    evalImport env imported to none [.expr "." args] = .ok [.imp to m (env.name m) none imported]) ∧
  (∀ env (imported : Bool) to (p : Ex), (match p with | .expr "." _ => false | .expr "as" _ => false | _ => true) = true →
    evalImport env imported to none [p] = .error (.errorException ("malformed \"" ++ (if imported then "import" else "using") ++ "\" statement"))) ∧
  (∀ env to args m, evalImportPathAll env to args "using" = .ok m → to ≠ env.main →
    evalUsing env to args = .ok [.use to m 0]) ∧
  (∀ env (a : String) m, a ≠ "." → evalImportPathAll env env.main [.sym a] "using" = .ok m →
    evalUsing env env.main [.sym a] = .ok [.use env.main m 0, .imp env.main m (env.name m) none true])

theorem importContract_proven : ImportContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro env at_ args kw m h; simp [evalImportPathAll, h, bind, Except.bind, pure, Except.pure]
  · intro env at_ args kw m v m' h h2; simp [evalImportPathAll, h, h2, bind, Except.bind, pure, Except.pure]
  · intro a b kw h
    unfold checkMacroRename
    by_cases ha : c1 a = 64
    · have hb := h.mp ha; simp [ha, hb]
    · have hb : ¬ c1 b = 64 := fun hb => ha (h.mpr hb); simp [ha, hb]
  · intro a b kw ha hb
    refine ⟨"cannot rename macro \"" ++ a ++ "\" to non-macro \"" ++ b ++ "\" in \"" ++ kw ++ "\"", ?_⟩
    simp [checkMacroRename, ha, hb]
  · intro a b kw ha hb
    refine ⟨"cannot rename non-macro \"" ++ a ++ "\" to macro \"" ++ b ++ "\" in \"" ++ kw ++ "\"", ?_⟩
    simp [checkMacroRename, ha, hb]
  · intro env imported to args m b _ hb h
    simp [evalImport, importOne, h, checkMacroRename, hb, bind, Except.bind, pure, Except.pure, List.mapM, List.mapM.loop]
  · intro env imported to args m b c hb hc h
    simp [evalImport, importOne, h, checkMacroRename, hb, hc, bind, Except.bind, pure, Except.pure, List.mapM,
      List.mapM.loop]
  · intro env imported to args m h
    simp [evalImport, importOne, h, bind, Except.bind, pure, Except.pure, List.mapM, List.mapM.loop]
  · intro env imported to p hp
    cases p with
    | expr hd as =>
      by_cases h1 : hd = "as"
      · subst h1; simp at hp
      · by_cases h2 : hd = "."
        · subst h2; simp at hp
        · cases imported <;> simp [evalImport, importOne, fail, h1, h2, bind, Except.bind, pure, Except.pure,
            List.mapM, List.mapM.loop]
    | _ => cases imported <;> simp [evalImport, importOne, fail, bind, Except.bind, pure, Except.pure,
        List.mapM, List.mapM.loop]
  · intro env to args m h hne
    simp [evalUsing, h, hne, bind, Except.bind, pure, Except.pure]
  · intro env a m ha h
    simp [evalUsing, h, Ex.isSym, ha, bind, Except.bind, pure, Except.pure]

end JuliaLean.MiscCov.Module
