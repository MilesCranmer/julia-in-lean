import JuliaLean.IOCov.Common

set_option linter.unusedSimpArgs false

/-!
Models of `base/env.jl` at master `bbfa0ce4150` (non-Windows branch). The process
environment is the C `environ` array, a list of byte strings. The libc calls follow
POSIX: `getenv(name)` returns the value of the first entry `name=value`;
`setenv(name, value, overwrite)` fails (`EINVAL`) for an empty name or one containing
`'='`, otherwise replaces the first entry for `name` (when `overwrite`) or appends one;
`unsetenv(name)` fails the same way, otherwise removes every entry for `name`.
`Cstring` conversion rejects strings containing NUL.
-/

namespace JuliaLean.IOCov.Env

open JuliaLean JuliaLean.IOCov

abbrev Bytes := List UInt8
abbrev Environ := List Bytes

def eqB : UInt8 := 61   -- '='

/-- `findfirst('=', env)` split: `(name, value)` of an entry with a `'='`. -/
def splitEntry (e : Bytes) : Option (Bytes × Bytes) :=
  match e.idxOf? eqB with
  | none => none
  | some k => some (e.take k, e.drop (k + 1))

/-- Value of `name` in an entry, as `getenv` matches it. -/
def entryValue (name : Bytes) (e : Bytes) : Option Bytes :=
  if (name ++ [eqB]).isPrefixOf e then some (e.drop (name.length + 1)) else none

/-- C `getenv(name)`; `none` is `C_NULL`. -/
def cgetenv (env : Environ) (name : Bytes) : Option Bytes :=
  env.findSome? (entryValue name)

def validName (name : Bytes) : Bool := !name.isEmpty && !name.contains eqB

/-- The first entry for `name` replaced by `new`. -/
def replaceFirst (name new : Bytes) : Environ → Environ
  | [] => []
  | e :: es => if (entryValue name e).isSome then new :: es else e :: replaceFirst name new es

/-- C `setenv(name, value, overwrite)`: `none` is the `-1` (`EINVAL`) return. -/
def csetenv (env : Environ) (name value : Bytes) (overwrite : Bool) : Option Environ :=
  if !validName name then none
  else match cgetenv env name with
    | none => some (env ++ [name ++ eqB :: value])
    | some _ => if overwrite then some (replaceFirst name (name ++ eqB :: value) env) else some env

/-- C `unsetenv(name)`. -/
def cunsetenv (env : Environ) (name : Bytes) : Option Environ :=
  if !validName name then none else some (env.filter (fun e => (entryValue name e).isNone))

/-- `Cstring` conversion of a Julia string argument. -/
def cstring (s : Bytes) : R Bytes :=
  if s.contains 0 then argErr "embedded NULs are not allowed in C strings" else .ok s

/-! ## Primitive accessors, lines 55-86 -/

/-- `_getenv(var) = getenv(var)`, line 55. -/
def getenvP (env : Environ) (var : Bytes) : R (Option Bytes) := do
  let v ← cstring var
  pure (cgetenv env v)
/-- `_hasenv(s) = _getenv(s) != C_NULL`, line 56. -/
def hasenv (env : Environ) (s : Bytes) : R Bool := do
  let r ← getenvP env s
  pure r.isSome
/-- `_environ()`, line 70 (Linux): the `environ` array. -/
def environ (env : Environ) : Environ := env
/-- `access_env(onError, var)`, lines 73-76. -/
def accessEnv {α} (env : Environ) (onError : Bytes → R α) (ofVal : Bytes → α) (var : Bytes) : R α := do
  let v ← getenvP env var
  match v with
  | none => onError var
  | some s => pure (ofVal s)
/-- `_setenv(var, val, overwrite)`, lines 78-81. -/
def setenvP (env : Environ) (var val : Bytes) (overwrite : Bool := true) : R Environ := do
  let k ← cstring var
  let v ← cstring val
  match csetenv env k v overwrite with
  | none => .error (.systemError "setenv")
  | some e => pure e
/-- `_unsetenv(var)`, lines 83-86. -/
def unsetenvP (env : Environ) (var : Bytes) : R Environ := do
  let k ← cstring var
  match cunsetenv env k with
  | none => .error (.systemError "unsetenv")
  | some e => pure e

/-! ## `EnvDict` methods, lines 179-191 -/

/-- `getindex(::EnvDict, k) = access_env(k->throw(KeyError(k)), k)`, line 179. -/
def getindex (env : Environ) (k : Bytes) : R Bytes :=
  accessEnv env (fun k => .error (.keyError k)) id k
/-- `get(::EnvDict, k, def) = access_env(Returns(def), k)`, line 180. -/
def get (env : Environ) (k def_ : Bytes) : R Bytes := accessEnv env (fun _ => .ok def_) id k
/-- `get(f, ::EnvDict, k) = access_env(k->f(), k)`, line 181. -/
def getF (env : Environ) (f : Unit → R Bytes) (k : Bytes) : R Bytes := accessEnv env (fun _ => f ()) id k
/-- `in(k, keys(ENV)) = _hasenv(k)`, line 186 (`haskey`). -/
def haskey (env : Environ) (k : Bytes) : R Bool := hasenv env k
/-- `setindex!(::EnvDict, v, k) = _setenv(k, string(v))`, line 190. -/
def setindex (env : Environ) (v k : Bytes) : R Environ := setenvP env k v
/-- `push!(::EnvDict, kv) = setindex!(ENV, kv.second, kv.first)`, line 191. -/
def push (env : Environ) (kv : Bytes × Bytes) : R Environ := setindex env kv.2 kv.1
/-- `delete!(::EnvDict, k) = (_unsetenv(k); ENV)`, line 189. -/
def delete (env : Environ) (k : Bytes) : R Environ := unsetenvP env k
/-- `pop!(::EnvDict, k) = (v = ENV[k]; _unsetenv(k); v)`, line 187. -/
def pop (env : Environ) (k : Bytes) : R (Bytes × Environ) := do
  let v ← getindex env k
  let e ← unsetenvP env k
  pure (v, e)
/-- `pop!(::EnvDict, k, def) = haskey(ENV,k) ? pop!(ENV,k) : def`, line 188. -/
def popDef (env : Environ) (k def_ : Bytes) : R (Bytes × Environ) := do
  let h ← haskey env k
  if h then pop env k else pure (def_, env)
/-- `get!(default, ::EnvDict, k)`, lines 182-185: `ENV[k] = default()` returns `default()`. -/
def getBang (env : Environ) (default : Unit → Bytes) (k : Bytes) : R (Bytes × Environ) := do
  let h ← haskey env k
  if h then do let v ← getindex env k; pure (v, env)
  else do let e ← setindex env (default ()) k; pure (default (), e)

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

/-! ## `get_bool_env`, `parse_bool_env`, lines 133-177 -/

def truthy : List Bytes := ["t", "T", "true", "True", "TRUE", "y", "Y", "yes", "Yes", "YES", "1"].map bs
def falsy : List Bytes := ["f", "F", "false", "False", "FALSE", "n", "N", "no", "No", "NO", "0"].map bs

/-- `parse_bool_env(name, val; throw)`, lines 167-177; `nothing` is `none`. -/
def parseBoolEnv (val : Bytes) (throw : Bool) : R (Option Bool) :=
  if val ∈ truthy then .ok (some true)
  else if val ∈ falsy then .ok (some false)
  else if throw then argErr "Value for environment variable could not be parsed as Boolean"
  else .ok none

/-- `get_bool_env(f_default, name; kwargs...)`, lines 158-166. -/
def getBoolEnvF (env : Environ) (fDefault : Unit → Option Bool) (name : Bytes) (throw : Bool) :
    R (Option Bool) := do
  let h ← haskey env name
  if h then
    let val ← getindex env name
    if !val.isEmpty then return (← parseBoolEnv val throw)
  pure (fDefault ())

/-- `get_bool_env(name, default; kwargs...)`, line 157. -/
def getBoolEnv (env : Environ) (name : Bytes) (default : Bool) (throw : Bool) : R (Option Bool) :=
  getBoolEnvF env (fun _ => some default) name throw

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

/-! ## Iteration, `length`, `show`, lines 231-262 -/

/-- `iterate(::EnvDict, i)`, lines 231-246: the entries from index `i`, split at the first
`'='`; entries without one are skipped (with a warning). -/
def iterateFrom (env : Environ) : List (Bytes × Bytes) := env.filterMap splitEntry

/-- `length(::EnvDict)`, lines 250-256: the number of iterated pairs. -/
def length (env : Environ) : Nat := (iterateFrom env).length

/-- `show(io, ::EnvDict)`, lines 258-262: one `k=v` line per pair. -/
def showEnv (env : Environ) : Bytes :=
  ((iterateFrom env).map (fun (k, v) => k ++ eqB :: v ++ [10])).flatten

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

/-! ## `withenv`, lines 277-290 -/

/-- One assignment of `withenv`: `val !== nothing ? (ENV[key]=val) : delete!(ENV, key)`. -/
def assign (env : Environ) (key : Bytes) (val : Option Bytes) : R Environ :=
  match val with
  | some v => setindex env v key
  | none => delete env key

/-- `old[key] = get(ENV, key, nothing)` for each pair, then the assignment. `old` is a
`Dict`: a later value for the same key replaces the earlier one in place. -/
def withenvSetup (env : Environ) : List (Bytes × Option Bytes) → List (Bytes × Option Bytes) →
    R (List (Bytes × Option Bytes) × Environ)
  | old, [] => .ok (old, env)
  | old, (key, val) :: rest => do
    let cur ← getenvP env key
    let old' := if old.any (·.1 == key) then old.map (fun p => if p.1 == key then (key, cur) else p)
      else old ++ [(key, cur)]
    let env' ← assign env key val
    withenvSetup env' old' rest

/-- Restoring loop of `withenv`'s `finally` block. -/
def restore (env : Environ) : List (Bytes × Option Bytes) → R Environ
  | [] => .ok env
  | (key, val) :: rest => do let e ← assign env key val; restore e rest

/-- `withenv(f, keyvals...)`, lines 277-289, with `f` not touching the environment. -/
def withenv (env : Environ) (kvs : List (Bytes × Option Bytes)) : R Environ := do
  let (old, env') ← withenvSetup env [] kvs
  restore env' old

/-- `withenv(f) = f()`, line 290. -/
def withenv0 (env : Environ) : Environ := env

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

