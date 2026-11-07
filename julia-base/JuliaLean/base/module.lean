import JuliaLean.Core
import JuliaLean.base.io

/-!
# Model of `base/module.jl`

The full-featured `_eval_import` and `_eval_using` of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`,
the lowered forms of `import`, `using` and `using A: x`. An import path is an `Expr` whose
arguments are symbols (names) or other values. Modules, global bindings, the loader (`require`)
and the `Core._import`/`Core._using` builtins are typed parameters with no assumed laws.
-/

namespace JuliaLean.base.module_

open JuliaLean
open JuliaLean.base.io (M Error)

/-- A value in an import `Expr`: a `Symbol`, a nested `Expr`, or a value of another type. -/
inductive Arg (V : Type) where
  | sym (name : String)
  | expr (head : String) (args : List (Arg V))
  | other (value : V)

/-- The modules `Mod` of the running session and the builtins acting on them. A global's value
has type `V`. -/
structure Modules (World Mod V : Type) where
  core : Mod
  base : Mod
  main : Mod
  sameModule : Mod → Mod → Bool
  /-- `v isa Module`. -/
  asModule : V → Option Mod
  require : Mod → String → M World V
  parentmodule : Mod → M World Mod
  getglobal : Mod → String → M World V
  nameof : Mod → M World String
  /-- `Core._import(to, from, asname, name, imported)` and `Core._import(to, from, asname)`. -/
  importName : Mod → Mod → String → String → Bool → M World Unit
  importModule : Mod → Mod → String → M World Unit
  /-- `Core._using(to, from, flags)`. -/
  usingModule : Mod → Mod → JInt .u8 → M World Unit
  /-- `TypeError(func, context, expected, got)` for a non-`Symbol` path element. -/
  typeError : String → Arg V → Error

section
variable {World Mod V : Type} (ms : Modules World Mod V)

def error (message : String) : Error := .errorException message

/-- `v === sym` for a path element. -/
def isSym {V : Type} (v : Arg V) (name : String) : Bool :=
  match v with
  | .sym s => s == name
  | _ => false

-- Reason: The opening comment and the loops that delete the bootstrap `_eval_import`/`_eval_using` methods are load-time method-table edits.
-- UNTRANSLATED
-- Source: base/module.jl:1-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Full-featured versions of _eval_import and _eval_using
-- 
-- for m in methods(_eval_import)
--     delete_method(m)
-- end
-- for m in methods(_eval_using)
--     delete_method(m)
-- end
-- 
-- /Source

/--
Julia source: base/module.jl:12-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eval_import_path(at::Module, from::Union{Module, Nothing}, path::Expr, keyword::String)
    isempty(path.args) && error("malformed import statement")

    i = RefValue(1)
    function next!()
        local v
        i[] <= length(path.args) || error("invalid module path")
        v = path.args[i[]]
        i[] += 1
        v isa Symbol || throw(TypeError(Symbol(keyword), "", Symbol, v))
        v
    end
    v = next!()

    if from !== nothing
        m = from
    elseif v !== :.
        # `A.B`: call the loader to obtain the root A in the current environment.
        if v === :Core
            m = Core
        elseif v === :Base
            m = Base
        else
            m = require(at, v)
            m isa Module || error("failed to load module $v")
        end
        i[] > lastindex(path.args) && return m, nothing
        v = next!()
    else
        # `.A.B.C`: strip off leading dots by following parent links
        m = at
        while (v = next!()) === :.
            m = parentmodule(m)
        end
    end

    while true
        v === :. && error("invalid $keyword path: \".\" in identifier path")
        i[] > lastindex(path.args) && break
        m = getglobal(m, v)
        m isa Module || error("invalid $keyword path: \"$v\" does not name a module")
        v = next!()
    end
    m, v
end
```
-/
def eval_import_path (atMod : Mod) (fromM : Option Mod) (args : List (Arg V)) (keyword : String) :
    M World (Mod × Option String) := do
  if args.isEmpty then throw (error "malformed import statement")
  -- `next!()`: the path element at `i[]`, as a `Symbol`, advancing `i[]`
  let next := fun (i : Nat) => do
    if !(i ≤ args.length) then throw (error "invalid module path")
    let v := args.getD (i - 1) (.sym "")
    match v with
    | .sym s => pure (s, i + 1)
    | _ => throw (ms.typeError keyword v)
  let (v, i) ← next 1
  let (m, v, i) ← match fromM with
    | some m => pure (m, v, i)
    | none =>
      if v != "." then do
        let m ← if v == "Core" then pure ms.core
          else if v == "Base" then pure ms.base
          else do
            match ms.asModule (← ms.require atMod v) with
            | some m => pure m
            | none => throw (error ("failed to load module " ++ v))
        if i > args.length then return (m, none)
        let (v, i) ← next i
        pure (m, v, i)
      else do
        JuliaLean.base.io.whileLoop (fun ((m, i) : Mod × Nat) => do
          let (v, i) ← next i
          if v == "." then return .inr (← ms.parentmodule m, i)
          return .inl (m, v, i)) (atMod, i)
  JuliaLean.base.io.whileLoop (fun ((m, v, i) : Mod × String × Nat) => do
    if v == "." then throw (error ("invalid " ++ keyword ++ " path: \".\" in identifier path"))
    if i > args.length then return .inl (m, some v)
    match ms.asModule (← ms.getglobal m v) with
    | none => throw (error ("invalid " ++ keyword ++ " path: \"" ++ v ++ "\" does not name a module"))
    | some m =>
      let (v, i) ← next i
      return .inr (m, v, i)) (m, v, i)

/--
Julia source: base/module.jl:57-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function eval_import_path_all(at::Module, path::Expr, keyword::String)
    m, v = eval_import_path(at, nothing, path, keyword)
    if v !== nothing
        m = getglobal(m, v)
        m isa Module || error("invalid $keyword path: \"$v\" does not name a module")
    end
    m
end
```
-/
def eval_import_path_all (atMod : Mod) (args : List (Arg V)) (keyword : String) : M World Mod := do
  let (m, v) ← eval_import_path ms atMod none args keyword
  match v with
  | none => return m
  | some v =>
    match ms.asModule (← ms.getglobal m v) with
    | some m => return m
    | none => throw (error ("invalid " ++ keyword ++ " path: \"" ++ v ++ "\" does not name a module"))

/-- `bitcast(Char, UInt32(unsafe_load(unsafe_convert(Ptr{UInt8}, sym))) << 24) == '@'`: whether
the first byte of the symbol's name (its terminating NUL for an empty name) is `@`. -/
def startsWithAt (name : String) : Bool := name.toUTF8.toList.head? == some 0x40

/--
Julia source: base/module.jl:66-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function check_macro_rename(from::Symbol, to::Symbol, keyword::String)
    c1(sym) = bitcast(Char, UInt32(unsafe_load(unsafe_convert(Ptr{UInt8}, sym))) << 24)
    from_c, to_c = c1(from), c1(to)
    if from_c == '@' && to_c != '@'
        error("cannot rename macro \"$from\" to non-macro \"$to\" in \"$keyword\"")
    end
    if from_c != '@' && to_c == '@'
        error("cannot rename non-macro \"$from\" to macro \"$to\" in \"$keyword\"")
    end
end

```
-/
def check_macro_rename (fromM toM keyword : String) : M World Unit := do
  let from_c := startsWithAt fromM
  let to_c := startsWithAt toM
  if from_c && !to_c then
    throw (error ("cannot rename macro \"" ++ fromM ++ "\" to non-macro \"" ++ toM ++ "\" in \"" ++
      keyword ++ "\""))
  if !from_c && to_c then
    throw (error ("cannot rename non-macro \"" ++ fromM ++ "\" to macro \"" ++ toM ++ "\" in \"" ++
      keyword ++ "\""))

/--
Julia source: base/module.jl:78-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    _eval_import(imported::Bool, to::Module, from::Union{Expr, Nothing}, paths::Expr...)

Evaluate the import paths, calling `Core._import` for each name to be imported.
`imported` imports are created with `import`, `using A: x` sets this to false.
The `from` is the part of the import path before the `:`.  This is the lowered
form of `import`, `import ...:`, and `using ...:`.

```
import A             => _eval_import(true,  Main, nothing,          Expr(:., :A))
import A.b           => _eval_import(true,  Main, nothing,          Expr(:., :A, :b))
import A.b as c      => _eval_import(true,  Main, nothing,          Expr(:as, Expr(:., :A, :b), :c))
import A.B: C.d, e   => _eval_import(true,  Main, Expr(:., :A, :B), Expr(:., :C, :d), Expr(:., :e))
import A.B: C.d as e => _eval_import(true,  Main, Expr(:., :A, :B), Expr(:as, Expr(:., :C, :d), :e))
using  A.B: C.d, e   => _eval_import(false, Main, Expr(:., :A, :B), Expr(:., :C, :d), Expr(:., :e))

See also [`_import`](@ref Core._import).
```
"""
function _eval_import(imported::Bool, to::Module, from::Union{Expr, Nothing}, paths::Expr...)
    keyword = imported ? "import" : "using"
    fail() = error("malformed \"$keyword\" statement")
    from = from !== nothing ? eval_import_path_all(to, from, keyword) : nothing

    for path in paths
        path isa Expr || fail()
        asname = nothing
        if path.head === :as && length(path.args) == 2
            path, asname = path.args
        elseif path.head !== :.
            fail()
        end
        m, name = eval_import_path(to, from, path, keyword)

        if name !== nothing
            asname = asname === nothing ? name : asname
            check_macro_rename(name, asname, keyword)
            Core._import(to, m, asname, name, imported)
        else
            Core._import(to, m, asname === nothing ? nameof(m) : asname)
        end
    end
end

````
-/
def eval_import (imported : Bool) (toM : Mod) (fromM : Option (List (Arg V))) (paths : List (Arg V)) :
    M World Unit := do
  let keyword := if imported then "import" else "using"
  let fail : M World Unit := throw (error ("malformed \"" ++ keyword ++ "\" statement"))
  let fromM ← match fromM with
    | some path => pure (some (← eval_import_path_all ms toM path keyword))
    | none => pure none
  for path in paths do
    let (args, asname) ← match path with
      | .expr "as" [inner, name] =>
        match inner with
        | .expr _ args => pure (args, some name)
        | _ => throw (.jl (.methodError "eval_import_path"))
      | .expr "." args => pure (args, none)
      | _ => do fail; pure ([], none)
    let (m, name) ← eval_import_path ms toM fromM args keyword
    match name with
    | some name =>
      let asname ← match asname with
        | none => pure name
        | some (.sym s) => pure s
        | some _ => throw (.jl (.methodError "check_macro_rename"))
      check_macro_rename name asname keyword
      ms.importName toM m asname name imported
    | none =>
      let asname ← match asname with
        | none => ms.nameof m
        | some (.sym s) => pure s
        | some other => throw (ms.typeError keyword other)
      ms.importModule toM m asname

/--
Julia source: base/module.jl:122-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    _eval_using(to::Module, path::Expr)

Evaluate the import path to a module and call [`Core._using`](@ref) on it,
making its exports available to the `to` module; this is the lowered form of
`using A`.

```
using A.B            => _eval_using(Main, Expr(:., :A, :B))
```

See also [`_using`](@ref Core._using).
"""
function _eval_using(to::Module, path::Expr, flags::UInt8=UInt8(0))
    from = eval_import_path_all(to, path, "using")
    Core._using(to, from, flags)
    is_package = length(path.args) == 1 && path.args[1] !== :.
    if to == Main && is_package
        Core._import(to, from, nameof(from))
    end
end
````
-/
def eval_using (toM : Mod) (args : List (Arg V)) (flags : JInt .u8 := JInt.lit .u8 0) :
    M World Unit := do
  let fromM ← eval_import_path_all ms toM args "using"
  ms.usingModule toM fromM flags
  let is_package := args.length == 1 && !isSym (args.getD 0 (.sym ".")) "."
  if ms.sameModule toM ms.main && is_package then
    ms.importModule toM fromM (← ms.nameof fromM)

end

end JuliaLean.base.module_


namespace JuliaLean.MiscCov.Module

open JuliaLean.MiscCov

/-- The value of a global: a module or anything else. -/
inductive GV where
  | mod (id : Nat)
  | other
  deriving DecidableEq, Repr

structure Env where
  core : Nat
  base : Nat
  main : Nat
  parent : Nat → Nat
  name : Nat → String
  getglobal : Nat → String → M GV
  require : Nat → String → M GV

/-- A recorded `Core._import(to, from, asname, name, imported)` (`name = none` for the
three-argument form) or `Core._using(to, from, flags)`. -/
inductive Call where
  | imp (to m : Nat) (asname : String) (name : Option String) (imported : Bool)
  | use (to m : Nat) (flags : Nat)
  deriving DecidableEq, Repr

/-- `next!()`, `base/module.jl:16-23`: the next path element as a symbol name, with the
advanced index (one-based). -/
def next (args : List Ex) (keyword : String) (i : Nat) : M (String × Nat) :=
  if i ≤ args.length then
    match args[i - 1]? with
    | some (.sym v) => .ok (v, i + 1)
    | _ => .error (.typeError)
  else .error (.errorException "invalid module path")

/-- The parent-link loop `while (v = next!()) === :.`, `base/module.jl:41-43`. -/
def dotLoop (env : Env) (args : List Ex) (keyword : String) : Nat → Nat → Nat → M (Nat × String × Nat)
  | 0, _, _ => .error (.other "fuel")
  | fuel + 1, m, i => do
    let (v, i) ← next args keyword i
    if v = "." then dotLoop env args keyword fuel (env.parent m) i else .ok (m, v, i)

/-- The `while true` loop, `base/module.jl:46-52`. -/
def walk (env : Env) (args : List Ex) (keyword : String) : Nat → Nat → String → Nat → M (Nat × Option String)
  | 0, _, _, _ => .error (.other "fuel")
  | fuel + 1, m, v, i =>
    if v = "." then .error (.errorException ("invalid " ++ keyword ++ " path: \".\" in identifier path"))
    else if i > args.length then .ok (m, some v)
    else do
      let g ← env.getglobal m v
      match g with
      | .mod m' => do
        let (v, i) ← next args keyword i
        walk env args keyword fuel m' v i
      | .other => .error (.errorException ("invalid " ++ keyword ++ " path: \"" ++ v ++ "\" does not name a module"))

/-- `eval_import_path(at, from, path, keyword)`, `base/module.jl:12-56`. -/
def evalImportPath (env : Env) (at_ : Nat) (from_ : Option Nat) (args : List Ex) (keyword : String) :
    M (Nat × Option String) :=
  if args.isEmpty then .error (.errorException "malformed import statement")
  else do
    let (v, i) ← next args keyword 1
    let fuel := args.length + 1
    match from_ with
    | some m => walk env args keyword fuel m v i
    | none =>
      if v ≠ "." then do
        let m ← (if v = "Core" then pure env.core else if v = "Base" then pure env.base else do
          match ← env.require at_ v with
          | .mod m => pure m
          | .other => .error (.errorException ("failed to load module " ++ v)) : M Nat)
        if i > args.length then .ok (m, none)
        else do
          let (v, i) ← next args keyword i
          walk env args keyword fuel m v i
      else do
        let (m, v, i) ← dotLoop env args keyword fuel at_ i
        walk env args keyword fuel m v i

/-- `eval_import_path_all(at, path, keyword)`, `base/module.jl:58-65`. -/
def evalImportPathAll (env : Env) (at_ : Nat) (args : List Ex) (keyword : String) : M Nat := do
  let (m, v) ← evalImportPath env at_ none args keyword
  match v with
  | none => pure m
  | some v =>
    match ← env.getglobal m v with
    | .mod m' => pure m'
    | .other => .error (.errorException ("invalid " ++ keyword ++ " path: \"" ++ v ++ "\" does not name a module"))

/-- `c1(sym)`, `base/module.jl:68`: the first byte of the symbol's name as a `Char`
(`'\0'` for the empty name). -/
def c1 (sym : String) : Nat := (sym.toUTF8.toList.headD 0).toNat

/-- `check_macro_rename(from, to, keyword)`, `base/module.jl:67-76`. -/
def checkMacroRename (from_ to : String) (keyword : String) : M Unit :=
  let fromC := c1 from_
  let toC := c1 to
  if fromC = 64 ∧ toC ≠ 64 then
    .error (.errorException ("cannot rename macro \"" ++ from_ ++ "\" to non-macro \"" ++ to ++ "\" in \"" ++ keyword ++ "\""))
  else if fromC ≠ 64 ∧ toC = 64 then
    .error (.errorException ("cannot rename non-macro \"" ++ from_ ++ "\" to macro \"" ++ to ++ "\" in \"" ++ keyword ++ "\""))
  else .ok ()

/-- `fail()`, `base/module.jl:99`. -/
def fail {α : Type} (keyword : String) : M α := .error (.errorException ("malformed \"" ++ keyword ++ "\" statement"))

/-- One path of `_eval_import`, `base/module.jl:102-119`. -/
def importOne (env : Env) (imported : Bool) (to : Nat) (from_ : Option Nat) (keyword : String) (path : Ex) :
    M Call := do
  let (path, asname) ← (match path with
    | .expr "as" [p, .sym a] => pure (p, some a)
    | .expr "as" [p, _] => do let _ ← (pure p : M Ex); .error .typeError
    | .expr "." _ => pure (path, none)
    | _ => fail keyword : M (Ex × Option String))
  let args ← (match path with
    | .expr "." args => pure args
    | _ => fail keyword : M (List Ex))
  let (m, name) ← evalImportPath env to from_ args keyword
  match name with
  | some name =>
    let asname := asname.getD name
    checkMacroRename name asname keyword
    pure (.imp to m asname (some name) imported)
  | none => pure (.imp to m (asname.getD (env.name m)) none imported)

/-- `_eval_import(imported, to, from, paths...)`, `base/module.jl:97-120`. -/
def evalImport (env : Env) (imported : Bool) (to : Nat) (from_ : Option (List Ex)) (paths : List Ex) :
    M (List Call) := do
  let keyword := if imported then "import" else "using"
  let from_ ← (match from_ with
    | some f => do pure (some (← evalImportPathAll env to f keyword))
    | none => pure none : M (Option Nat))
  paths.mapM (importOne env imported to from_ keyword)

/-- `_eval_using(to, path, flags)`, `base/module.jl:135-142`. -/
def evalUsing (env : Env) (to : Nat) (args : List Ex) (flags : Nat := 0) : M (List Call) := do
  let from_ ← evalImportPathAll env to args "using"
  let isPackage := args.length == 1 && !(args.headD .nothing).isSym "."
  pure ([.use to from_ flags] ++ if to = env.main && isPackage then [.imp to from_ (env.name from_) none true] else [])

end JuliaLean.MiscCov.Module
