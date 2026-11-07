import JuliaLean.base.env
import JuliaLean.Proofs.base.io.IOCovCommon


section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Env

open JuliaLean JuliaLean.IOCov

/-- Valid environment variable name and value: nonempty name without `'='`, no NULs. -/
def Valid (k v : Bytes) : Prop := validName k = true ∧ ¬ k.contains 0 ∧ ¬ v.contains 0

theorem cstring_ok (s : Bytes) (h : ¬ s.contains 0) : cstring s = .ok s := by
  unfold cstring; rw [if_neg h]

theorem cstring_nul (s : Bytes) (h : s.contains 0) :
    cstring s = argErr "embedded NULs are not allowed in C strings" := by
  unfold cstring; rw [if_pos h]

theorem entryValue_self (k v : Bytes) : entryValue k (k ++ eqB :: v) = some v := by
  simp [entryValue, List.isPrefixOf_iff_prefix]

theorem validName_noEq (k : Bytes) (h : validName k = true) : eqB ∉ k := by
  simp [validName] at h; simpa using h.2

theorem cgetenv_append_none (env : Environ) (k x : Bytes) (h : cgetenv env k = none) :
    cgetenv (env ++ [x]) k = entryValue k x := by
  induction env with
  | nil => cases h' : entryValue k x <;> simp [cgetenv, List.findSome?, h']
  | cons e es ih =>
    simp only [cgetenv, List.findSome?_cons, List.cons_append] at h ⊢
    cases he : entryValue k e with
    | none => rw [he] at h; simp only at h ⊢; exact ih h
    | some _ => rw [he] at h; simp at h

theorem cgetenv_replaceFirst (env : Environ) (k v : Bytes) (h : (cgetenv env k).isSome) :
    cgetenv (replaceFirst k (k ++ eqB :: v) env) k = some v := by
  induction env with
  | nil => simp [cgetenv] at h
  | cons e es ih =>
    simp only [replaceFirst]
    cases he : entryValue k e with
    | some _ => simp [cgetenv, entryValue_self]
    | none =>
      simp only [he, Option.isSome_none, Bool.false_eq_true, if_false]
      simp only [cgetenv, List.findSome?_cons, he] at h ⊢
      exact ih h

theorem cgetenv_filter (env : Environ) (k : Bytes) :
    cgetenv (env.filter (fun e => (entryValue k e).isNone)) k = none := by
  induction env with
  | nil => rfl
  | cons e es ih =>
    cases he : entryValue k e with
    | none =>
      simp only [List.filter_cons, he, Option.isNone_none, if_true, cgetenv, List.findSome?_cons]
      exact ih
    | some _ =>
      simp only [List.filter_cons, he, Option.isNone_some, Bool.false_eq_true, if_false]
      exact ih

/-- `ENV[k] = v` then `ENV[k]` gives `v`; `delete!(ENV, k)` then `haskey(ENV, k)` is false;
`pop!` returns the value and removes the key; `get` falls back to the default. -/
def EnvDictCorrect : Prop :=
  (∀ env k v, Valid k v → ∃ e', setindex env v k = .ok e' ∧ getindex e' k = .ok v) ∧
  (∀ env k, validName k = true → ¬ k.contains 0 →
      ∃ e', delete env k = .ok e' ∧ haskey e' k = .ok false) ∧
  (∀ env k, ¬ k.contains 0 → cgetenv env k = none → getindex env k = .error (.keyError k)) ∧
  (∀ env k d, ¬ k.contains 0 → get env k d = .ok ((cgetenv env k).getD d)) ∧
  (∀ env f k, ¬ k.contains 0 → cgetenv env k = none → getF env f k = f ()) ∧
  (∀ env k, ¬ k.contains 0 → haskey env k = .ok (cgetenv env k).isSome) ∧
  (∀ env k v, push env (k, v) = setindex env v k) ∧
  (∀ env k, k.contains 0 → getindex env k = argErr "embedded NULs are not allowed in C strings") ∧
  (∀ env k v, ¬ k.contains 0 → ¬ v.contains 0 → validName k = false →
      setindex env v k = .error (.systemError "setenv")) ∧
  (∀ env k v, validName k = true → ¬ k.contains 0 → cgetenv env k = some v →
      ∃ e', pop env k = .ok (v, e') ∧ cgetenv e' k = none) ∧
  (∀ env k d, ¬ k.contains 0 → cgetenv env k = none → popDef env k d = .ok (d, env)) ∧
  (∀ env k v, ¬ k.contains 0 → cgetenv env k = some v → getBang env (fun _ => []) k = .ok (v, env)) ∧
  (∀ env, environ env = env)

theorem envDictCorrect : EnvDictCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
  · intro env k v hv
    obtain ⟨hk, hk0, hv0⟩ := hv
    cases hg : cgetenv env k with
    | none =>
      refine ⟨env ++ [k ++ eqB :: v], ?_, ?_⟩
      · simp [setindex, setenvP, cstring_ok k hk0, cstring_ok v hv0, csetenv, hk, hg,
          bind, Except.bind, pure, Except.pure]
      · simp [getindex, accessEnv, getenvP, cstring_ok k hk0, cgetenv_append_none env k _ hg,
          entryValue_self, bind, Except.bind, pure, Except.pure]
    | some w =>
      refine ⟨replaceFirst k (k ++ eqB :: v) env, ?_, ?_⟩
      · simp [setindex, setenvP, cstring_ok k hk0, cstring_ok v hv0, csetenv, hk, hg,
          bind, Except.bind, pure, Except.pure]
      · have := cgetenv_replaceFirst env k v (by simp [hg])
        simp [getindex, accessEnv, getenvP, cstring_ok k hk0, this, bind, Except.bind, pure,
          Except.pure]
  · intro env k hk hk0
    refine ⟨env.filter (fun e => (entryValue k e).isNone), ?_, ?_⟩
    · simp [delete, unsetenvP, cstring_ok k hk0, cunsetenv, hk, bind, Except.bind, pure, Except.pure]
    · simp [haskey, hasenv, getenvP, cstring_ok k hk0, cgetenv_filter, bind, Except.bind, pure,
        Except.pure]
  · intro env k hk0 h
    simp [getindex, accessEnv, getenvP, cstring_ok k hk0, h, bind, Except.bind, pure, Except.pure]
  · intro env k d hk0
    cases h : cgetenv env k <;>
      simp [get, accessEnv, getenvP, cstring_ok k hk0, h, bind, Except.bind, pure, Except.pure]
  · intro env f k hk0 h
    simp only [getF, accessEnv, getenvP, cstring_ok k hk0, h, bind, Except.bind, pure, Except.pure]
  · intro env k hk0
    simp [haskey, hasenv, getenvP, cstring_ok k hk0, bind, Except.bind, pure, Except.pure]
  · intro env k h
    simp [getindex, accessEnv, getenvP, cstring_nul k h, argErr, bind, Except.bind]
  · intro env k v hk0 hv0 hk
    simp [setindex, setenvP, cstring_ok k hk0, cstring_ok v hv0, csetenv, hk, bind, Except.bind,
      pure, Except.pure]
  · intro env k v hk hk0 h
    refine ⟨env.filter (fun e => (entryValue k e).isNone), ?_, cgetenv_filter env k⟩
    simp [pop, getindex, accessEnv, getenvP, unsetenvP, cunsetenv, cstring_ok k hk0, h, hk,
      bind, Except.bind, pure, Except.pure]
  · intro env k d hk0 h
    simp [popDef, haskey, hasenv, getenvP, cstring_ok k hk0, h, bind, Except.bind, pure, Except.pure]
  · intro env k v hk0 h
    simp [getBang, haskey, hasenv, getindex, accessEnv, getenvP, cstring_ok k hk0, h, bind,
      Except.bind, pure, Except.pure]

/-- Documented: truthy strings give `true`, falsy ones `false`, others `nothing` (or an
error with `throw=true`); an unset or empty variable gives the default. -/
def BoolEnvDoc : Prop :=
  (∀ v ∈ truthy, ∀ t, parseBoolEnv v t = .ok (some true)) ∧
  (∀ v ∈ falsy, ∀ t, parseBoolEnv v t = .ok (some false)) ∧
  (∀ v, v ∉ truthy → v ∉ falsy → parseBoolEnv v false = .ok none ∧
      ∃ m, parseBoolEnv v true = argErr m) ∧
  (∀ env name d t, ¬ name.contains 0 → cgetenv env name = none → getBoolEnv env name d t = .ok (some d)) ∧
  (∀ env name d t, ¬ name.contains 0 → cgetenv env name = some [] → getBoolEnv env name d t = .ok (some d)) ∧
  (∀ env name d t v, ¬ name.contains 0 → cgetenv env name = some v → v ≠ [] →
      getBoolEnv env name d t = parseBoolEnv v t)

theorem truthy_falsy_disjoint : ∀ v ∈ truthy, v ∉ falsy := by decide

theorem boolEnvDoc : BoolEnvDoc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv t; simp [parseBoolEnv, hv]
  · intro v hv t
    have : v ∉ truthy := fun h => truthy_falsy_disjoint v h hv
    simp [parseBoolEnv, hv, this]
  · intro v h1 h2
    exact ⟨by simp [parseBoolEnv, h1, h2], "Value for environment variable could not be parsed as Boolean",
      by simp [parseBoolEnv, h1, h2]⟩
  · intro env name d t h0 h
    simp [getBoolEnv, getBoolEnvF, haskey, hasenv, getenvP, cstring_ok name h0, h, bind,
      Except.bind, pure, Except.pure]
  · intro env name d t h0 h
    simp [getBoolEnv, getBoolEnvF, haskey, hasenv, getindex, accessEnv, getenvP,
      cstring_ok name h0, h, bind, Except.bind, pure, Except.pure]
  · intro env name d t v h0 h hv
    have hv' : v.isEmpty = false := by cases v <;> simp_all
    simp only [getBoolEnv, getBoolEnvF, haskey, hasenv, getindex, accessEnv, getenvP,
      cstring_ok name h0, h, hv', bind, Except.bind, pure, Except.pure, Option.isSome_some, if_true,
      id, Bool.not_false]

def EnvIterationCorrect : Prop :=
  (∀ env k v, (k, v) ∈ iterateFrom env → eqB ∉ k ∧ k ++ eqB :: v ∈ env) ∧
  (∀ env, length env = (env.filter (fun e => e.contains eqB)).length) ∧
  (∀ env k v, validName k = true → eqB ∉ v → iterateFrom (env ++ [k ++ eqB :: v]) = iterateFrom env ++ [(k, v)]) ∧
  (∀ env, showEnv env = ((iterateFrom env).map (fun (k, v) => k ++ eqB :: v ++ [10])).flatten)

theorem splitEntry_some (e k v : Bytes) (h : splitEntry e = some (k, v)) : eqB ∉ k ∧ k ++ eqB :: v = e := by
  unfold splitEntry at h
  cases hi : e.idxOf? eqB with
  | none => simp [hi] at h
  | some n =>
    simp [hi] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlt := List.idxOf?_eq_some_iff.mp hi
    obtain ⟨hlt, hget, hbefore⟩ := hlt
    refine ⟨?_, ?_⟩
    · intro hm
      obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hm
      simp at hj
      have := hbefore j (by omega)
      simp [List.getElem_take] at hjv
      exact this (by simpa using hjv)
    · conv => rhs; rw [← List.take_append_drop n e]
      congr 1
      rw [List.drop_eq_getElem_cons hlt, hget]

theorem splitEntry_none_iff (e : Bytes) : splitEntry e = none ↔ eqB ∉ e := by
  unfold splitEntry
  cases hi : e.idxOf? eqB with
  | none => simp [List.idxOf?_eq_none_iff.mp hi]
  | some n =>
    simp
    have := (List.idxOf?_eq_some_iff.mp hi)
    exact List.mem_of_getElem this.2.1

theorem splitEntry_kv (k v : Bytes) (hk : eqB ∉ k) : splitEntry (k ++ eqB :: v) = some (k, v) := by
  unfold splitEntry
  have : (k ++ eqB :: v).idxOf? eqB = some k.length := by
    rw [List.idxOf?_eq_some_iff]
    refine ⟨by simp, by simp, ?_⟩
    intro j hj
    simp [List.getElem_append_left hj]
    intro h; exact hk (h ▸ List.getElem_mem hj)
  simp [this]

theorem envIterationCorrect : EnvIterationCorrect := by
  refine ⟨?_, ?_, ?_, fun _ => rfl⟩
  · intro env k v h
    simp [iterateFrom, List.mem_filterMap] at h
    obtain ⟨e, he, hs⟩ := h
    obtain ⟨h1, h2⟩ := splitEntry_some e k v hs
    exact ⟨h1, h2 ▸ he⟩
  · intro env
    simp only [length, iterateFrom]
    induction env with
    | nil => rfl
    | cons e es ih =>
      simp only [List.filterMap_cons, List.filter_cons]
      cases hs : splitEntry e with
      | none =>
        have := (splitEntry_none_iff e).mp hs
        simp [this, ih]
      | some kv =>
        have : eqB ∈ e := Classical.byContradiction fun hn => by
          rw [(splitEntry_none_iff e).mpr hn] at hs; simp at hs
        simp [this, ih]
  · intro env k v hk _
    simp [iterateFrom, List.filterMap_append, splitEntry_kv k v (validName_noEq k hk)]

/-- Documented: "When `withenv` returns, the original environment has been restored."
Stated for every variable named in `kvs`, with valid names and values. -/
def WithenvRestores : Prop :=
  ∀ env (kvs : List (Bytes × Option Bytes)),
    (∀ p ∈ kvs, validName p.1 = true ∧ ¬ p.1.contains 0 ∧ ∀ v, p.2 = some v → ¬ v.contains 0) →
    ∃ env', withenv env kvs = .ok env' ∧ ∀ p ∈ kvs, cgetenv env' p.1 = cgetenv env p.1

def WithenvSingle : Prop :=
  (∀ env, withenv0 env = env) ∧
  ∀ env k (val : Option Bytes), validName k = true → ¬ k.contains 0 → (∀ v, val = some v → ¬ v.contains 0) →
    (∀ o, cgetenv env k = some o → ¬ o.contains 0) →
    ∃ env', withenv env [(k, val)] = .ok env' ∧ cgetenv env' k = cgetenv env k

theorem withenvRestores_refuted : ¬ WithenvRestores := by
  intro h
  obtain ⟨env', h1, h2⟩ := h [] [(bs "X", some (bs "1")), (bs "X", some (bs "2"))] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩ <;> intro v hv <;> cases hv <;> decide)
  have hw : withenv [] [(bs "X", some (bs "1")), (bs "X", some (bs "2"))] = .ok [bs "X=1"] := by rfl
  rw [hw] at h1
  cases h1
  have h3 := h2 _ (List.mem_cons_self ..)
  revert h3; decide

theorem set_lookup (env : Environ) (k v : Bytes) (hk : validName k = true) (hk0 : ¬ k.contains 0)
    (hv0 : ¬ v.contains 0) : ∃ e', setindex env v k = .ok e' ∧ cgetenv e' k = some v := by
  cases hg : cgetenv env k with
  | none =>
    refine ⟨env ++ [k ++ eqB :: v], ?_, ?_⟩
    · simp [setindex, setenvP, cstring_ok k hk0, cstring_ok v hv0, csetenv, hk, hg,
        bind, Except.bind, pure, Except.pure]
    · simp [cgetenv_append_none env k _ hg, entryValue_self]
  | some w =>
    refine ⟨replaceFirst k (k ++ eqB :: v) env, ?_, cgetenv_replaceFirst env k v (by simp [hg])⟩
    simp [setindex, setenvP, cstring_ok k hk0, cstring_ok v hv0, csetenv, hk, hg,
      bind, Except.bind, pure, Except.pure]

theorem del_lookup (env : Environ) (k : Bytes) (hk : validName k = true) (hk0 : ¬ k.contains 0) :
    ∃ e', delete env k = .ok e' ∧ cgetenv e' k = none :=
  ⟨env.filter (fun e => (entryValue k e).isNone),
    by simp [delete, unsetenvP, cstring_ok k hk0, cunsetenv, hk, bind, Except.bind, pure, Except.pure],
    cgetenv_filter env k⟩

theorem assign_lookup (env : Environ) (k : Bytes) (val : Option Bytes) (hk : validName k = true)
    (hk0 : ¬ k.contains 0) (hv : ∀ v, val = some v → ¬ v.contains 0) :
    ∃ e', assign env k val = .ok e' ∧ cgetenv e' k = val := by
  cases val with
  | none => exact del_lookup env k hk hk0
  | some v => exact set_lookup env k v hk hk0 (hv v rfl)

theorem withenvSingle : WithenvSingle := by
  refine ⟨fun _ => rfl, ?_⟩
  intro env k val hk hk0 hv ho
  obtain ⟨e1, he1, _⟩ := assign_lookup env k val hk hk0 hv
  obtain ⟨e2, he2, hl2⟩ := assign_lookup e1 k (cgetenv env k) hk hk0 ho
  refine ⟨e2, ?_, hl2⟩
  simp [withenv, withenvSetup, restore, getenvP, cstring_ok k hk0, he1, he2, bind, Except.bind,
    pure, Except.pure]

/-! ## Per-method properties -/

def EnvDictCorrect_1 : Prop :=
  (∀ env k v, Valid k v → ∃ e', setindex env v k = .ok e' ∧ getindex e' k = .ok v)
theorem envDictCorrect_1 : EnvDictCorrect_1 := by
  have h := envDictCorrect
  exact h.1

def EnvDictCorrect_2 : Prop :=
  (∀ env k, validName k = true → ¬ k.contains 0 →
      ∃ e', delete env k = .ok e' ∧ haskey e' k = .ok false)
theorem envDictCorrect_2 : EnvDictCorrect_2 := by
  have h := envDictCorrect
  exact h.2.1

def EnvDictCorrect_3 : Prop :=
  (∀ env k, ¬ k.contains 0 → cgetenv env k = none → getindex env k = .error (.keyError k))
theorem envDictCorrect_3 : EnvDictCorrect_3 := by
  have h := envDictCorrect
  exact h.2.2.1

def EnvDictCorrect_4 : Prop :=
  (∀ env k d, ¬ k.contains 0 → get env k d = .ok ((cgetenv env k).getD d))
theorem envDictCorrect_4 : EnvDictCorrect_4 := by
  have h := envDictCorrect
  exact h.2.2.2.1

def EnvDictCorrect_5 : Prop :=
  (∀ env f k, ¬ k.contains 0 → cgetenv env k = none → getF env f k = f ())
theorem envDictCorrect_5 : EnvDictCorrect_5 := by
  have h := envDictCorrect
  exact h.2.2.2.2.1

def EnvDictCorrect_6 : Prop :=
  (∀ env k, ¬ k.contains 0 → haskey env k = .ok (cgetenv env k).isSome)
theorem envDictCorrect_6 : EnvDictCorrect_6 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.1

def EnvDictCorrect_7 : Prop :=
  (∀ env k v, push env (k, v) = setindex env v k)
theorem envDictCorrect_7 : EnvDictCorrect_7 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.2.1

def EnvDictCorrect_8 : Prop :=
  (∀ env k, k.contains 0 → getindex env k = argErr "embedded NULs are not allowed in C strings")
theorem envDictCorrect_8 : EnvDictCorrect_8 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.2.2.1

def EnvDictCorrect_9 : Prop :=
  (∀ env k v, ¬ k.contains 0 → ¬ v.contains 0 → validName k = false →
      setindex env v k = .error (.systemError "setenv"))
theorem envDictCorrect_9 : EnvDictCorrect_9 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.2.2.2.1

def EnvDictCorrect_10 : Prop :=
  (∀ env k v, validName k = true → ¬ k.contains 0 → cgetenv env k = some v →
      ∃ e', pop env k = .ok (v, e') ∧ cgetenv e' k = none)
theorem envDictCorrect_10 : EnvDictCorrect_10 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.2.2.2.2.1

def EnvDictCorrect_11 : Prop :=
  (∀ env k d, ¬ k.contains 0 → cgetenv env k = none → popDef env k d = .ok (d, env))
theorem envDictCorrect_11 : EnvDictCorrect_11 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.2.2.2.2.2.1

def EnvDictCorrect_12 : Prop :=
  (∀ env k v, ¬ k.contains 0 → cgetenv env k = some v → getBang env (fun _ => []) k = .ok (v, env))
theorem envDictCorrect_12 : EnvDictCorrect_12 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.2.2.2.2.2.2.1

def EnvDictCorrect_13 : Prop :=
  (∀ env, environ env = env)
theorem envDictCorrect_13 : EnvDictCorrect_13 := by
  have h := envDictCorrect
  exact h.2.2.2.2.2.2.2.2.2.2.2.2

def BoolEnvDoc_1 : Prop :=
  (∀ v ∈ truthy, ∀ t, parseBoolEnv v t = .ok (some true))
theorem boolEnvDoc_1 : BoolEnvDoc_1 := by
  have h := boolEnvDoc
  exact h.1

def BoolEnvDoc_2 : Prop :=
  (∀ v ∈ falsy, ∀ t, parseBoolEnv v t = .ok (some false))
theorem boolEnvDoc_2 : BoolEnvDoc_2 := by
  have h := boolEnvDoc
  exact h.2.1

def BoolEnvDoc_3 : Prop :=
  (∀ v, v ∉ truthy → v ∉ falsy → parseBoolEnv v false = .ok none ∧
      ∃ m, parseBoolEnv v true = argErr m)
theorem boolEnvDoc_3 : BoolEnvDoc_3 := by
  have h := boolEnvDoc
  exact h.2.2.1

def BoolEnvDoc_4 : Prop :=
  (∀ env name d t, ¬ name.contains 0 → cgetenv env name = none → getBoolEnv env name d t = .ok (some d))
theorem boolEnvDoc_4 : BoolEnvDoc_4 := by
  have h := boolEnvDoc
  exact h.2.2.2.1

def BoolEnvDoc_5 : Prop :=
  (∀ env name d t, ¬ name.contains 0 → cgetenv env name = some [] → getBoolEnv env name d t = .ok (some d))
theorem boolEnvDoc_5 : BoolEnvDoc_5 := by
  have h := boolEnvDoc
  exact h.2.2.2.2.1

def BoolEnvDoc_6 : Prop :=
  (∀ env name d t v, ¬ name.contains 0 → cgetenv env name = some v → v ≠ [] →
      getBoolEnv env name d t = parseBoolEnv v t)
theorem boolEnvDoc_6 : BoolEnvDoc_6 := by
  have h := boolEnvDoc
  exact h.2.2.2.2.2

def EnvIterationCorrect_1 : Prop :=
  (∀ env k v, (k, v) ∈ iterateFrom env → eqB ∉ k ∧ k ++ eqB :: v ∈ env)
theorem envIterationCorrect_1 : EnvIterationCorrect_1 := by
  have h := envIterationCorrect
  exact h.1

def EnvIterationCorrect_2 : Prop :=
  (∀ env, length env = (env.filter (fun e => e.contains eqB)).length)
theorem envIterationCorrect_2 : EnvIterationCorrect_2 := by
  have h := envIterationCorrect
  exact h.2.1

def EnvIterationCorrect_3 : Prop :=
  (∀ env k v, validName k = true → eqB ∉ v → iterateFrom (env ++ [k ++ eqB :: v]) = iterateFrom env ++ [(k, v)])
theorem envIterationCorrect_3 : EnvIterationCorrect_3 := by
  have h := envIterationCorrect
  exact h.2.2.1

def EnvIterationCorrect_4 : Prop :=
  (∀ env, showEnv env = ((iterateFrom env).map (fun (k, v) => k ++ eqB :: v ++ [10])).flatten)
theorem envIterationCorrect_4 : EnvIterationCorrect_4 := by
  have h := envIterationCorrect
  exact h.2.2.2

def WithenvSingle_1 : Prop :=
  (∀ env, withenv0 env = env)
theorem withenvSingle_1 : WithenvSingle_1 := by
  have h := withenvSingle
  exact h.1

def WithenvSingle_2 : Prop :=
  ∀ env k (val : Option Bytes), validName k = true → ¬ k.contains 0 → (∀ v, val = some v → ¬ v.contains 0) →
    (∀ o, cgetenv env k = some o → ¬ o.contains 0) →
    ∃ env', withenv env [(k, val)] = .ok env' ∧ cgetenv env' k = cgetenv env k
theorem withenvSingle_2 : WithenvSingle_2 := by
  have h := withenvSingle
  exact h.2
end JuliaLean.IOCov.Env
end
