import JuliaLean.base.error
import JuliaLean.Core
import JuliaLean.base.dict
import JuliaLean.base.show
import JuliaLean.base.strings.string

/-!
# Model of `base/methodshow.jl`

Typed model of the methods of `base/methodshow.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on 64-bit Linux. Each modelled method is a Lean definition whose docstring carries the method's
verbatim source; its body follows the Julia body call by call.

* Output uses the `base/show.jl` model: a stream is a `JIO`, the stream primitives are `IOPrims`,
  and `print(io, xs...)` is `printAll`. The monad `m` throws show.jl's `ShowError` and this
  file's `MethodShowError` (`error(msg)`).
* `Method`, `Module`, Julia types, `TypeVar`s, `TypeName`s and `MethodList`s are abstract types;
  their fields and the runtime reflection the methods use (`jl_uncompress_argnames`,
  `jl_methtable_lookup`, `unwrap_unionall`, `Vararg` parameters, subtyping against
  `Tuple{Core.Builtin, Vararg}`) are the fields of `Reflect`.
* Callees defined in files loaded later (`printstyled` of `base/util.jl`, `print_module_path_file`,
  `get_stacktrace_color` and `parentmodule_before_main` of `base/errorshow.jl`,
  `find_source_file` of `base/loading.jl`), show.jl methods whose model uses another
  representation (`sprint` of `show_sym`, `show_signature_function`, `string_with_env`), `show` of
  a `TypeVar` or `Module`, the `Sys` path constants, the function object held by
  `methodloc_callback` and the `LibGit2` stdlib are the fields of `Callees`. A Julia `String`
  result is `Bytes` (it may hold invalid UTF-8). `try … catch end` catches the exception type `Ex`
  of every exception `m` throws.
-/

namespace JuliaLean.base.methodshow

open JuliaLean
open JuliaLean.base.show
open JuliaLean.base.dict (ImmutableDict ValueConv)

/-- `error(msg)`: `ErrorException`. -/
inductive MethodShowError where
  | errorException (msg : String)
  deriving Repr, DecidableEq

/-- An argument of `string_with_env(env, xs...)`: a string, a type, or a `Vararg` length. -/
inductive EnvPiece (Ty VN : Type) where
  | str (s : String)
  | ty (t : Ty)
  | n (n : VN)

/-- The argument name passed to `argtype_decl`: a `Symbol`, an `Expr` (`n::T` in the argument
list, by its `n.args[1]`), or another value. -/
inductive ArgName where
  | sym (s : Sym)
  | expr (arg1 : ArgName)
  | other

/-- Reflection on methods, method tables and types. `Meth` is `Method`, `Mod` `Module`, `Ty` a
Julia type, `TV` a `TypeVar`, `VN` the `N` parameter of a `Vararg`, `TN` a `TypeName`, `ML` a
`MethodList`, `MT` a `Core.MethodTable`, `MI` a `Core.MethodInstance`. -/
structure Reflect (m : Type → Type) (V Ty Meth Mod TV VN TN ML MT MI : Type) where
  /-- The fields `m.sig`, `m.name`, `m.file`, `m.line`, `m.nargs`, `m.isva`. -/
  sig : Meth → Ty
  name : Meth → Sym
  file : Meth → Sym
  line : Meth → JInt .i32
  nargs : Meth → JInt64
  isva : Meth → Bool
  /-- `ccall(:jl_uncompress_argnames, Vector{Symbol}, (Any,), m.slot_syms)`. -/
  uncompress_argnames : Meth → List Sym
  parentmodule : Meth → Mod
  /-- `get_methodtable(m)`. -/
  get_methodtable : Meth → m (Option MT)
  /-- `isa(t, UnionAll)`: its `var` and `body`. -/
  unionAll : Ty → Option (TV × Ty)
  /-- `t.parameters` of a `DataType`; throws for other types. -/
  parameters : Ty → m (List Ty)
  unwrap_unionall : Ty → Ty
  /-- `rewrap_unionall(t, u)`. -/
  rewrap_unionall : Ty → Ty → Ty
  /-- `Tuple{ts...}`. -/
  tupleOf : List Ty → Ty
  unwrapva : Ty → Ty
  isvarargtype : Ty → Bool
  /-- `t.N` of a `Vararg` when `isdefined(t, :N)`. -/
  varargN : Ty → Option VN
  /-- `va.N` when it is an `Int`. -/
  vnInt : VN → Option JInt64
  /-- `Vararg{t, n}`; throws for an invalid `n`. -/
  mkVararg : Ty → JInt64 → m Ty
  /-- `t === Any`. -/
  isAny : Ty → Bool
  /-- `t === Tuple`. -/
  isTuple : Ty → Bool
  /-- `t <: Tuple{Core.Builtin, Vararg}`. -/
  isBuiltinSig : Ty → m Bool
  /-- `typeof(Core.kwcall)` and `NamedTuple`. -/
  kwcallType : Ty
  namedTuple : Ty
  /-- `p isa TypeEq` and then `type_parameter(p)` if it is a `Type` (`some (some tp)`), or not a
  type (`some none`). -/
  typeEqParameter : Ty → Option (Option Ty)
  has_free_typevars : Ty → Bool
  /-- `Core.TypeEgal{tp}`. -/
  typeEgal : Ty → Ty
  /-- `ccall(:jl_methtable_lookup, Any, (Any, UInt), sig, world)`: a `Method` or `nothing`. -/
  methtable_lookup : Ty → JInt .u64 → m (Option Meth)
  /-- A `TypeVar` stored as an `Any` value. -/
  ofTV : TV → V
  /-- `ms.tn` and the methods of a `MethodList`. -/
  tn : ML → TN
  methods : ML → List Meth
  /-- `tn.singletonname`, `tn.module`, `tn.wrapper <: Core.Builtin`, `iskindtype(tn.wrapper)`. -/
  singletonname : TN → Sym
  tnModule : TN → Mod
  wrapperIsBuiltin : TN → m Bool
  wrapperIsKind : TN → Bool
  /-- `isdefined(mod, name) && typeof(getfield(mod, name)) <: Function`. -/
  hasFunctionBinding : Mod → Sym → m Bool
  /-- `mod === Core`, `mod == Base`. -/
  isCore : Mod → Bool
  isBase : Mod → Bool
  /-- `parentmodule(mod)` and `===` on modules. -/
  parentmoduleMod : Mod → Mod
  egalMod : Mod → Mod → Bool
  /-- `mt.module`, `mt.name`, `length(mt)` of a `Core.MethodTable`. -/
  mtModule : MT → Mod
  mtName : MT → Sym
  mtLength : MT → JInt64
  /-- `mi.def` of a `MethodInstance`, when it is a `Method`. -/
  miDef : MI → Option Meth

/-- `LibGit2` operations used by `url` over `String` bytes; resources are closed by `close`. -/
structure LibGit2Ops (m : Type → Type) (Repo Cfg : Type) where
  GitRepoExt : Bytes → m Repo
  GitConfig : Repo → m Cfg
  get : Cfg → Bytes → Bytes → m Bytes
  /-- `(match(LibGit2.GITHUB_REGEX, u)::AbstractMatch).captures[1]`. -/
  githubCapture : Bytes → m Bytes
  /-- `string(LibGit2.head_oid(repo))`. -/
  head_oid : Repo → m Bytes
  path : Repo → m Bytes
  realpath : Bytes → m Bytes
  closeRepo : Repo → m Unit
  closeCfg : Cfg → m Unit

/-- The value a function stored in `methodloc_callback` returns, before the assertion. -/
inductive LocFile where
  | sym (s : Sym)
  | str (b : Bytes)
  | other

inductive LocLine where
  | i32 (n : JInt .i32)
  | i64 (n : JInt64)
  | other

/-- The `Sys`/`Base` path constants and `base/path.jl` functions `fixup_stdlib_path` reads. -/
structure StdlibPaths (m : Type → Type) where
  /-- `Sys.BUILD_STDLIB_PATH`, `Sys.STDLIB`, `Sys.BINDIR`, `Base.DATAROOTDIR`. -/
  BUILD_STDLIB_PATH : Bytes
  STDLIB : Bytes
  BINDIR : Bytes
  DATAROOTDIR : Bytes
  /-- `dirname(String(Base.moduleloc(Core.Compiler).file))` when `Core.Compiler` is defined. -/
  compiler_folder : Option Bytes
  /-- `normpath`, `dirname`, `basename`, `abspath` of `base/path.jl` and `replace(s, a => b)`. -/
  normpath : Bytes → m Bytes
  dirname : Bytes → Bytes
  basename : Bytes → Bytes
  abspath : List Bytes → m Bytes
  replace : Bytes → Bytes → Bytes → m Bytes

/-- Callees in other files and show.jl methods. `String` results are `Bytes` (a `String` may hold
invalid UTF-8). `Col` is a stacktrace color (`Symbol` or `Int`); `Fn` a function object stored in
`methodloc_callback`. -/
structure Callees (m : Type → Type) (Io V Ty Meth Mod TV VN Col Fn : Type) where
  /-- `sprint(show_sym, s)`. -/
  sprint_show_sym : Sym → m Bytes
  /-- `string_with_env(env, xs...)`. -/
  string_with_env : ImmutableDict Sym V → List (EnvPiece Ty VN) → m Bytes
  /-- `sprint(show_signature_function, ft, false, fargname, html, context = env)`. -/
  sprint_show_signature_function : ImmutableDict Sym V → Ty → Bool → Bytes → Bool → m Bytes
  /-- `show(io, tv)` of a `TypeVar`, `print(io, mod)` of a `Module`. -/
  showTV : JIO Io V → TV → m Unit
  printModule : JIO Io V → Mod → m Unit
  /-- `printstyled` (`base/util.jl`). -/
  printstyled : PrintStyled m Io V
  /-- `print_module_path_file(io, modul, file, line; modulecolor, digit_align_width)`. -/
  print_module_path_file : JIO Io V → Mod → Bytes → JInt .i32 → Option Col → JInt64 → m Unit
  get_stacktrace_color : Mod → m Col
  parentmodule_before_main : Mod → m Mod
  /-- `printstyled(io, xs...; color=col)` with a stacktrace color. -/
  printstyled_color : JIO Io V → List (JIO Io V → m Unit) → Col → m Unit
  /-- `:light_black`. -/
  light_black : Col
  /-- `find_source_file(path)` (`base/loading.jl`). -/
  find_source_file : Bytes → m (Option Bytes)
  /-- `print_type_bicolor`'s string operations. -/
  bytes : BytesOps m
  /-- `methodloc_callback[]`: the function object in the `Ref`, or `nothing`. -/
  methodloc_callback : m (Option Fn)
  /-- `invokelatest(f, m)` of that function object. -/
  invokelatest : Fn → Meth → m (LocFile × LocLine)
  paths : StdlibPaths m
  /-- `Sys.iswindows()`, `Base.GIT_VERSION_INFO.commit`, `VERSION`. -/
  iswindows : Bool
  git_commit : Bytes
  version : Bytes
  /-- `maybe_root_module(LibGit2 id) isa Module`: the stdlib's operations. -/
  libgit2 : Option (Σ Repo Cfg : Type, LibGit2Ops m Repo Cfg)
  /-- `summary(io, mt)` of a `Vector{Method}`. -/
  summary : JIO Io V → List Meth → m Unit
  /-- `push!(v, (file, line))` and `empty!(v)` of the `:last_shown_line_infos` vector. -/
  push_line_info : V → Bytes × JInt .i32 → m Unit
  empty_line_infos : V → m Unit
  /-- `isa(f, Function)` of a Julia value. -/
  isFunction : V → m Bool

section
/- `Ex` is the type of every exception `m` throws: `try … catch end` catches it. -/
variable {m : Type → Type} [Monad m] [MonadExceptOf ShowError m] [MonadExceptOf MethodShowError m]
  {Ex : Type} [MonadExceptOf Ex m] {Io V Ty Meth Mod TV VN TN ML MT MI Col Fn : Type}

def jlerror {α : Type} (msg : String) : m α := throwThe MethodShowError (.errorException msg)

/-- `xs[i]` (1-based); `BoundsError` outside `1:length(xs)`. -/
def idx {α : Type} (xs : List α) (i : Int) : m α :=
  if h : 1 ≤ i ∧ i ≤ xs.length then pure (xs[(i - 1).toNat]'(by omega))
  else throwShow (.jl .boundsError)

/-- The decimal digits of an `Int` (`string(n)`). -/
def decStr {t : IntTy} (n : JInt t) : String := toString n.val

/-- `print(io, n)` of an `Int`: `show(io, n) = write(io, string(n))`. -/
def printIntS (p : IOPrims m Io V) (io : JIO Io V) {t : IntTy} (n : JInt t) : m Unit := printStr p io (decStr n)

-- UNTRANSLATED
-- license header and file comment; no method
-- Source: base/methodshow.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Method and method table pretty-printing
-- 
-- /Source

/--
Julia source: base/methodshow.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const empty_sym = Symbol("")
```
-/
def empty_sym : Sym := ""

/-- `replace(s, r"^(.*)#(.*#)?\d+$"sa => s"\1")`. The pattern is anchored at the start; its greedy
`(.*)` ends at the last `#` from which the rest matches, so it matches exactly when the text after
the last `#` is one or more ASCII digits, optionally followed by a final newline (where `$` also
matches), and the replacement keeps the text before that `#`. -/
def gensymReplace (s : String) : String :=
  let cs := s.toList
  match cs.reverse.findIdx? (· == '#') with
  | none => s
  | some k =>
    let cut := cs.length - 1 - k
    let tail := cs.drop (cut + 1)
    let digits := if tail.getLast? == some '\n' then tail.dropLast else tail
    if !digits.isEmpty && digits.all (fun c => '0' ≤ c && c ≤ '9') then String.ofList (cs.take cut) else s

/--
Julia source: base/methodshow.jl:6-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function strip_gensym(sym)
    if sym === :var"#self#" || sym === :var"#unused#"
        return empty_sym
    end
    return Symbol(replace(String(sym), r"^(.*)#(.*#)?\d+$"sa => s"\1"))
end

```
-/
def strip_gensym : ArgName → m Sym
  | .sym sym =>
    if sym == "#self#" || sym == "#unused#" then
      return empty_sym
    else
      return gensymReplace sym
  -- `String(sym)` has no method for an `Expr` or other value
  | _ => throwShow (.jl (.methodError "String"))

/--
Julia source: base/methodshow.jl:13-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function argtype_decl(env, n, @nospecialize(sig::DataType), i::Int, nargs, isva::Bool) # -> (argname, argtype)
    t = unwrapva(sig.parameters[min(i, end)])
    if i == nargs && isva
        va = sig.parameters[end]
        if isvarargtype(va) && (!isdefined(va, :N) || !isa(va.N, Int))
            t = va
        else
            ntotal = length(sig.parameters)
            isvarargtype(va) && (ntotal += va.N - 1)
            t = Vararg{t,ntotal-nargs+1}
        end
    end
    if isa(n,Expr)
        n = n.args[1]  # handle n::T in arg list
    end
    n = strip_gensym(n)
    local s
    if n === empty_sym
        s = ""
    else
        s = sprint(show_sym, n)
        t === Any && return s, ""
    end
    if isvarargtype(t)
        if !isdefined(t, :N)
            if unwrapva(t) === Any
                return string(s, "..."), ""
            else
                return s, string_with_env(env, unwrapva(t)) * "..."
            end
        end
        return s, string_with_env(env, "Vararg{", t.T, ", ", t.N, "}")
    end
    return s, string_with_env(env, t)
end

```
-/
def argtype_decl (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (c : Callees m Io V Ty Meth Mod TV VN Col Fn)
    (env : ImmutableDict Sym V) (n : ArgName) (sig : Ty) (i : JInt64) (nargs : JInt64) (isva : Bool) :
    m (Bytes × Bytes) := do
  let ps ← r.parameters sig
  let mut t := r.unwrapva (← idx ps (min i.val ps.length))
  if i.val == nargs.val && isva then
    let va ← idx ps ps.length
    let vaN : Option JInt64 := (r.varargN va).bind r.vnInt
    if r.isvarargtype va && vaN.isNone then
      t := va
    else
      let mut ntotal : JInt64 := JInt.wrap .i64 ps.length
      if r.isvarargtype va then
        if let some N := vaN then
          ntotal := JInt.wrap .i64 (ntotal.val + (JInt.wrap .i64 (N.val - 1)).val)
      t ← r.mkVararg t (JInt.wrap .i64 ((JInt.wrap .i64 (ntotal.val - nargs.val)).val + 1))
  let n := match n with
    | .expr arg1 => arg1 -- handle n::T in arg list
    | n => n
  let n ← strip_gensym n
  let mut s : Bytes := []
  if n == empty_sym then
    s := []
  else
    s ← c.sprint_show_sym n
    if r.isAny t then return (s, [])
  if r.isvarargtype t then
    match r.varargN t with
    | none =>
      if r.isAny (r.unwrapva t) then
        return (s ++ lit "...", [])
      else
        return (s, (← c.string_with_env env [.ty (r.unwrapva t)]) ++ lit "...")
    | some N =>
      return (s, ← c.string_with_env env [.str "Vararg{", .ty (r.unwrapva t), .str ", ", .n N, .str "}"])
  return (s, ← c.string_with_env env [.ty t])

/--
Julia source: base/methodshow.jl:49-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function method_argnames(m::Method)
    argnames = ccall(:jl_uncompress_argnames, Vector{Symbol}, (Any,), m.slot_syms)
    isempty(argnames) && return argnames
    return argnames[1:m.nargs]
end

```
-/
def method_argnames (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (meth : Meth) : m (List Sym) := do
  let argnames := r.uncompress_argnames meth
  if argnames.isEmpty then return argnames
  -- `argnames[1:m.nargs]`
  let n := (r.nargs meth).val
  if n > argnames.length then throwShow (.jl .boundsError)
  return argnames.take n.toNat

/-- The `while isa(sig, UnionAll)` loop of `arg_decl_parts`. -/
def unionall_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (tv : List TV) (sig : Ty) : m (List TV × Ty) := do
  let u ← pure (r.unionAll sig)
  match u with
  | some vb => unionall_loop r (tv ++ [vb.1]) vb.2
  | none => pure (tv, sig)
partial_fixpoint

/-- The `for t in tv` loop of `arg_decl_parts`. -/
def show_env_loop (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (show_env : ImmutableDict Sym V) :
    List TV → m (ImmutableDict Sym V)
  | [] => pure show_env
  | t :: ts => do
    let show_env ← ofDict (JuliaLean.base.dict.immutablePrepend (JuliaLean.base.dict.fieldConv Sym)
      (JuliaLean.base.dict.fieldConv V) show_env "unionall_env" (r.ofTV t))
    show_env_loop r show_env ts

/--
Julia source: base/methodshow.jl:145-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# In case the line numbers in the source code have changed since the code was compiled,
# allow packages to set a callback function that corrects them.
# (Used by Revise and perhaps other packages.)
# Any function `f` stored here must be consistent with the signature
#    f(m::Method)::Tuple{Union{Symbol,String}, Union{Int32,Int64}}
const methodloc_callback = Ref{Union{Function, Nothing}}(nothing)

```
-/
-- `methodloc_callback[]` is `Callees.methodloc_callback`, initially `nothing`.
def methodloc_callback_initial {Meth : Type} : Option (Meth → m (String × JInt64)) := none

/--
Julia source: base/methodshow.jl:152-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fixup_stdlib_path(path::String)
    # The file defining Base.Sys gets included after this file is included so make sure
    # this function is valid even in this intermediary state
    if isdefined(@__MODULE__, :Sys)
        if Sys.BUILD_STDLIB_PATH != Sys.STDLIB
            # BUILD_STDLIB_PATH gets defined in sysinfo.jl
            npath = normpath(path)
            npath′ = replace(npath, normpath(Sys.BUILD_STDLIB_PATH) => normpath(Sys.STDLIB))
            path = npath == npath′ ? path : npath′
        end
        if isdefined(@__MODULE__, :Core) && isdefined(Core, :Compiler)
            compiler_folder = dirname(String(Base.moduleloc(Core.Compiler).file))
            if dirname(path) == compiler_folder
                return abspath(Sys.BINDIR, Base.DATAROOTDIR, "julia", "Compiler", "src", basename(path))
            end
        end
    end
    return path
end

```
-/
def fixup_stdlib_path (sp : StdlibPaths m) (path : Bytes) : m Bytes := do
  let mut path := path
  -- The file defining Base.Sys gets included after this file is included so make sure
  -- this function is valid even in this intermediary state
  -- (`isdefined(@__MODULE__, :Sys)` holds at run time)
  if sp.BUILD_STDLIB_PATH != sp.STDLIB then
    -- BUILD_STDLIB_PATH gets defined in sysinfo.jl
    let npath ← sp.normpath path
    let npath' ← sp.replace npath (← sp.normpath sp.BUILD_STDLIB_PATH) (← sp.normpath sp.STDLIB)
    path := if npath == npath' then path else npath'
  if let some compiler_folder := sp.compiler_folder then
    if sp.dirname path == compiler_folder then
      return ← sp.abspath [sp.BINDIR, sp.DATAROOTDIR, lit "julia", lit "Compiler", lit "src", sp.basename path]
  return path

/--
Julia source: base/methodshow.jl:172-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This function does the method location updating
function updated_methodloc(m::Method)::Tuple{String, Int32}
    file, line = m.file, m.line
    if methodloc_callback[] !== nothing
        try
            file, line = invokelatest(methodloc_callback[], m)::Tuple{Union{Symbol,String}, Union{Int32,Int64}}
        catch
        end
    end
    file = fixup_stdlib_path(string(file))
    return file, Int32(line)
end

```
-/
def updated_methodloc (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (meth : Meth) : m (Bytes × JInt .i32) := do
  let mut file : LocFile := .sym (r.file meth)
  let mut line : LocLine := .i32 (r.line meth)
  if (← c.methodloc_callback).isSome then
    -- `try … catch end` ignores every exception, including a failed type assertion of the result
    let call : m (Option (LocFile × LocLine)) := do
      let some f ← c.methodloc_callback | throwShow .typeError
      let (fl, ln) ← c.invokelatest f meth
      -- `::Tuple{Union{Symbol,String}, Union{Int32,Int64}}`
      match fl, ln with
      | .other, _ | _, .other => throwShow .typeError
      | _, _ => pure (some (fl, ln))
    let res ← tryCatchThe Ex call (fun _ => pure none)
    if let some fl := res then
      file := fl.1
      line := fl.2
  -- `string(file)`
  let fileBytes := match file with
    | .sym s => lit s
    | .str b => b
    | .other => []
  let fileBytes ← fixup_stdlib_path c.paths fileBytes
  -- `Int32(line)` throws `InexactError` outside the `Int32` range
  match line with
  | .i32 n => return (fileBytes, n)
  | .i64 n =>
    if n.val < IntTy.min .i32 || n.val > IntTy.max .i32 then throwShow (.jl (.inexactError "Int32"))
    return (fileBytes, JInt.wrap .i32 n.val)
  | .other => throwShow .typeError

/-- `decls = [argtype_decl(show_env, argnames[i], sig, i, m.nargs, m.isva) for i = 1:m.nargs]`. -/
def decls_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (c : Callees m Io V Ty Meth Mod TV VN Col Fn)
    (show_env : ImmutableDict Sym V) (argnames : List Sym) (sig : Ty) (nargs : JInt64) (isva : Bool) :
    Nat → m (List (Bytes × Bytes))
  | 0 => pure []
  | k + 1 => do
    let earlier ← decls_loop r c show_env argnames sig nargs isva k
    let i : JInt64 := JInt.wrap .i64 (k + 1)
    let d ← argtype_decl r c show_env (.sym (← idx argnames (k + 1))) sig i nargs isva
    return earlier ++ [d]

/--
Julia source: base/methodshow.jl:55-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function arg_decl_parts(m::Method, html=false)
    tv = Any[]
    sig = m.sig
    while isa(sig, UnionAll)
        push!(tv, sig.var)
        sig = sig.body
    end
    file, line = updated_methodloc(m)
    argnames = method_argnames(m)
    if length(argnames) >= m.nargs
        show_env = ImmutableDict{Symbol, Any}()
        for t in tv
            show_env = ImmutableDict(show_env, :unionall_env => t)
        end
        decls = Tuple{String,String}[argtype_decl(show_env, argnames[i], sig, i, m.nargs, m.isva)
                    for i = 1:m.nargs]
        decls[1] = ("", sprint(show_signature_function, unwrapva(sig.parameters[1]), false, decls[1][1], html,
                               context = show_env))
    else
        decls = Tuple{String,String}[("", "") for _ = 1:length(sig.parameters::SimpleVector)]
    end
    return tv, decls, file, line
end

```
-/
def arg_decl_parts [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (c : Callees m Io V Ty Meth Mod TV VN Col Fn)
    (meth : Meth) (html : Bool := false) : m (List TV × List (Bytes × Bytes) × Bytes × JInt .i32) := do
  let (tv, sig) ← unionall_loop r [] (r.sig meth)
  let (file, line) ← updated_methodloc (Ex := Ex) c r meth
  let argnames ← method_argnames r meth
  let mut decls : List (Bytes × Bytes) := []
  if argnames.length ≥ (r.nargs meth).val then
    let show_env ← show_env_loop r [] tv
    decls ← decls_loop r c show_env argnames sig (r.nargs meth) (r.isva meth) (r.nargs meth).val.toNat
    let ft := r.unwrapva (← idx (← r.parameters sig) 1)
    let d1 ← idx decls 1
    let s ← c.sprint_show_signature_function show_env ft false d1.1 html
    decls := ([], s) :: decls.drop 1
  else
    -- `length(sig.parameters::SimpleVector)`
    decls := (← r.parameters sig).map fun _ => ([], [])
  return (tv, decls, file, line)

/-- The `for p in sig_params` loop of `kwarg_decl`: the new parameters and `changed`. -/
def typeegal_params (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (new_params : List Ty) (changed : Bool) :
    List Ty → List Ty × Bool
  | [] => (new_params, changed)
  | p :: ps =>
    match r.typeEqParameter p with
    | some (some tp) =>
      if !r.has_free_typevars tp then typeegal_params r (new_params ++ [r.typeEgal tp]) true ps
      else typeegal_params r (new_params ++ [p]) changed ps
    | _ => typeegal_params r (new_params ++ [p]) changed ps

/-- `filter(x -> !(x === empty_sym || '#' in string(x)), names)`. -/
def kwNames (names : List Sym) : List Sym :=
  names.filter fun x => !(x == empty_sym || x.toList.contains '#')

/--
Julia source: base/methodshow.jl:79-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# NOTE: second argument is deprecated and is no longer used
function kwarg_decl(m::Method, kwtype = nothing; world::UInt=get_world_counter())
    if !(m.sig === Tuple || m.sig <: Tuple{Core.Builtin, Vararg}) # OpaqueClosure or Builtin
        kwtype = typeof(Core.kwcall)
        sig_params = (unwrap_unionall(m.sig)::DataType).parameters
        sig = rewrap_unionall(Tuple{kwtype, NamedTuple, sig_params...}, m.sig)
        kwli = ccall(:jl_methtable_lookup, Any, (Any, UInt), sig, world)
        if kwli === nothing
            # a compiled keyword sorter is specialized on the dispatch (egality)
            # spelling of closed type-valued slots, so retry the lookup with
            # `Type{X}` slots as `Core.TypeEgal{X}`
            new_params = Any[kwtype, NamedTuple]
            changed = false
            for p in sig_params
                if p isa TypeEq
                    tp = type_parameter(p)
                    if tp isa Type && !has_free_typevars(tp)
                        p = Core.TypeEgal{tp}
                        changed = true
                    end
                end
                push!(new_params, p)
            end
            if changed
                sig = rewrap_unionall(Tuple{new_params...}, m.sig)
                kwli = ccall(:jl_methtable_lookup, Any, (Any, UInt), sig, world)
            end
        end
        if kwli !== nothing
            kwli = kwli::Method
            slotnames = ccall(:jl_uncompress_argnames, Vector{Symbol}, (Any,), kwli.slot_syms)
            kws = filter(x -> !(x === empty_sym || '#' in string(x)), slotnames[(kwli.nargs + 1):end])
            # ensure the kwarg... is always printed last. The order of the arguments are not
            # necessarily the same as defined in the function
            i = findfirst(x -> endswith(string(x)::String, "..."), kws)
            if i !== nothing
                push!(kws, kws[i])
                deleteat!(kws, i)
            end
            isempty(kws) && push!(kws,  :var"...")
            return kws
        end
    end
    return Symbol[]
end

```
-/
def kwarg_decl (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (meth : Meth) (world : JInt .u64) : m (List Sym) := do
  if !(← (if r.isTuple (r.sig meth) then pure true else r.isBuiltinSig (r.sig meth))) then -- OpaqueClosure or Builtin
    let kwtype := r.kwcallType
    let sig_params ← r.parameters (r.unwrap_unionall (r.sig meth))
    let sig := r.rewrap_unionall (r.tupleOf ([kwtype, r.namedTuple] ++ sig_params)) (r.sig meth)
    let mut kwli ← r.methtable_lookup sig world
    if kwli.isNone then
      -- a compiled keyword sorter is specialized on the dispatch (egality)
      -- spelling of closed type-valued slots, so retry the lookup with
      -- `Type{X}` slots as `Core.TypeEgal{X}`
      let (new_params, changed) := typeegal_params r [kwtype, r.namedTuple] false sig_params
      if changed then
        let sig := r.rewrap_unionall (r.tupleOf new_params) (r.sig meth)
        kwli ← r.methtable_lookup sig world
    if let some k := kwli then
      let slotnames := r.uncompress_argnames k
      let mut kws := kwNames (slotnames.drop (r.nargs k).val.toNat)
      -- ensure the kwarg... is always printed last. The order of the arguments are not
      -- necessarily the same as defined in the function
      match kws.findIdx? (fun x => x.endsWith "...") with
      | some i =>
        kws := kws ++ [kws.getD i ""]
        kws := kws.eraseIdx i
      | none => pure ()
      if kws.isEmpty then kws := kws ++ ["..."]
      return kws
  return []

/-- The `for i = 1:length(tv)` loop of `show_method_params`. -/
def show_method_params_loop (p : IOPrims m Io V) (a : AnyOps V Ty) (ofTV : TV → V)
    (showTV : JIO Io V → TV → m Unit) (io : JIO Io V) (first : Bool) : List TV → m (JIO Io V)
  | [] => pure io
  | x :: xs => do
    if !first then
      printStr p io ", "
    showTV io x
    let io : JIO Io V := .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym)
      (JuliaLean.base.dict.fieldConv V) io ("unionall_env", ofTV x))
    show_method_params_loop p a ofTV showTV io false xs

/--
Julia source: base/methodshow.jl:125-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_method_params(io::IO, tv)
    if !isempty(tv)
        print(io, " where ")
        if length(tv) == 1
            show(io, tv[1])
        else
            print(io, "{")
            for i = 1:length(tv)
                if i > 1
                    print(io, ", ")
                end
                x = tv[i]
                show(io, x)
                io = IOContext(io, :unionall_env => x)
            end
            print(io, "}")
        end
    end
end

```
-/
def show_method_params (p : IOPrims m Io V) (a : AnyOps V Ty) (ofTV : TV → V)
    (showTV : JIO Io V → TV → m Unit) (io : JIO Io V) (tv : List TV) : m Unit := do
  if !tv.isEmpty then
    printStr p io " where "
    match tv with
    | [x] => showTV io x
    | _ =>
      printStr p io "{"
      let io ← show_method_params_loop p a ofTV showTV io true tv
      printStr p io "}"

/--
Julia source: base/methodshow.jl:187-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    functionloc(m::Method)

Return a tuple `(filename,line)` giving the location of a `Method` definition.
"""
function functionloc(m::Method)
    file, ln = updated_methodloc(m)
    if ln <= 0
        error("could not determine location of method definition")
    end
    return (find_source_file(string(file)), ln)
end

```
-/
def functionloc_Method [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (meth : Meth) : m (Option Bytes × JInt .i32) := do
  let (file, ln) ← updated_methodloc (Ex := Ex) c r meth
  if ln.val ≤ 0 then
    jlerror "could not determine location of method definition"
  return (← c.find_source_file file, ln)

/--
Julia source: base/methodshow.jl:185-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
functionloc(m::Core.MethodInstance) = functionloc(m.def)

```
-/
def functionloc_MethodInstance [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (mi : MI) : m (Option Bytes × JInt .i32) := do
  match r.miDef mi with
  | some meth => functionloc_Method (Ex := Ex) c r meth
  -- `m.def` is a `Module` for a toplevel thunk; `functionloc` has no `Module` method
  | none => throwShow (.jl (.methodError "functionloc"))

/--
Julia source: base/methodshow.jl:200-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    functionloc(f::Function, types)

Return a tuple `(filename,line)` giving the location of a generic `Function` definition.
"""
functionloc(@nospecialize(f), @nospecialize(types)) = functionloc(which(f,types))
functionloc(@nospecialize(argtypes::Union{Tuple, Type{<:Tuple}})) = functionloc(which(argtypes))

```
-/
-- `which(f, types)` and `which(argtypes)` (`base/reflection.jl`) are the parameter `which`.
-- `which(f, types)` and `which(argtypes)` (`base/reflection.jl`) are the parameter `which`.
def functionloc_types {X : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (which : X → m Meth) (x : X) : m (Option Bytes × JInt .i32) := do
  functionloc_Method (Ex := Ex) c r (← which x)

/--
Julia source: base/methodshow.jl:208-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function functionloc(@nospecialize(f))
    mt = methods(f)
    if isempty(mt)
        if isa(f, Function)
            error("function has no definitions")
        else
            error("object is not callable")
        end
    end
    if length(mt) > 1
        error("function has multiple methods; please specify a type signature")
    end
    return functionloc(first(mt))
end

```
-/
-- `methods(f)` (`base/reflection.jl`) is the parameter `methods`.
def functionloc_f [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (methods : V → m ML) (f : V) : m (Option Bytes × JInt .i32) := do
  let mt := r.methods (← methods f)
  if mt.isEmpty then
    if ← c.isFunction f then
      jlerror "function has no definitions"
    else
      jlerror "object is not callable"
  if mt.length > 1 then
    jlerror "function has multiple methods; please specify a type signature"
  functionloc_Method (Ex := Ex) c r (← idx mt 1)

/-- `s[1:end-3]` of a `String` ending in `"..."`: a `StringIndexError` when the byte before the
dots is not the last byte of a character. -/
def dropDots (s : String) : m String := do
  let bs := s.toUTF8.toList
  let j := bs.length - 3
  -- `isvalid(s, j)`: byte `j` starts a character
  let jValid := j == 0 || (match bs[j - 1]? with
    | some b => b &&& 0xC0 != 0x80
    | none => false)
  if !jValid then throwShow .stringIndexError
  -- the bytes `1:j` end at a character boundary of the valid string `s`
  return String.fromUTF8! ⟨(bs.take j).toArray⟩

/--
Julia source: base/methodshow.jl:223-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sym_to_string(sym)
    if sym === :var"..."
        return "..."
    end
    s = String(sym)
    if endswith(s, "...")
        return string(sprint(show_sym, Symbol(s[1:end-3])), "...")
    else
        return sprint(show_sym, sym)
    end
end

```
-/
def sym_to_string (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (sym : Sym) : m Bytes := do
  if sym == "..." then
    return lit "..."
  let s := sym
  if s.endsWith "..." then
    return (← c.sprint_show_sym (← dropDots s)) ++ lit "..."
  else
    return ← c.sprint_show_sym sym

/-- The `for (i,d) in enumerate(decls[2:end])` loop of `show_method`. -/
def show_method_args (p : IOPrims m Io V) (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (io : JIO Io V)
    (ndecls : Nat) : Nat → List (Bytes × Bytes) → m Unit
  | _, [] => pure ()
  | i, d :: ds => do
    c.printstyled io [fun io => printBytes p io d.1] "light_black" false
    if !d.2.isEmpty then
      printStr p io "::"
      print_type_bicolor_String p c.printstyled c.bytes io d.2 "bold" "normal"
    if i < ndecls - 1 then printStr p io ", "
    show_method_args p c io ndecls (i + 1) ds

/-- The `for kw in kwargs` loop of `show_method`. -/
def show_method_kwargs (p : IOPrims m Io V) (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (io : JIO Io V)
    (lastkw : Sym) : List Sym → m Unit
  | [] => pure ()
  | kw :: kws => do
    let skw ← sym_to_string c kw
    printBytes p io skw
    if kw != lastkw then
      printStr p io ", "
    show_method_kwargs p c io lastkw kws

/--
Julia source: base/methodshow.jl:240-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_method(io::IO, m::Method;
                     modulecolor = :light_black, digit_align_width = 1,
                     print_signature_only::Bool = get(io, :print_method_signature_only, false)::Bool)
    tv, decls, file, line = arg_decl_parts(m)
    if m.sig <: Tuple{Core.Builtin, Vararg}
        # Builtin
        print(io, m.name, "(...)")
        file = "none"
        line = 0
    else
        print(io, decls[1][2], "(")

        # arguments
        for (i,d) in enumerate(decls[2:end])
            printstyled(io, d[1], color=:light_black)
            if !isempty(d[2])
                print(io, "::")
                print_type_bicolor(io, d[2], color=:bold, inner_color=:normal)
            end
            i < length(decls)-1 && print(io, ", ")
        end

        kwargs = kwarg_decl(m)
        if !isempty(kwargs)
            print(io, "; ")
            for kw in kwargs
                skw = sym_to_string(kw)
                print(io, skw)
                if kw != last(kwargs)
                    print(io, ", ")
                end
            end
        end
        print(io, ")")
        show_method_params(io, tv)
    end

    if !print_signature_only
        if !(get(io, :compact, false)::Bool) # single-line mode
            println(io)
            digit_align_width += 4
        end
        # module & file, re-using function from errorshow.jl
        print_module_path_file(io, parentmodule(m), string(file), line; modulecolor, digit_align_width)
    end
end

```
-/
def show_method [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (meth : Meth)
    (modulecolor : Option Col := some c.light_black) (digit_align_width : JInt64 := JInt.wrap .i64 1)
    (print_signature_only : Option Bool := none) : m Unit := do
  let print_signature_only ← match print_signature_only with
    | some b => pure b
    | none => assertBool a (getIO p io "print_method_signature_only" false)
  let mut digit_align_width := digit_align_width
  let (tv, decls, file0, line0) ← arg_decl_parts (Ex := Ex) r c meth
  let mut file := file0
  let mut line := line0
  if ← r.isBuiltinSig (r.sig meth) then
    -- Builtin
    printAll p io [print_Symbol p io (r.name meth), printStr p io "(...)"]
    file := lit "none"
    line := JInt.wrap .i32 0
  else
    let d1 ← idx decls 1
    printAll p io [printBytes p io d1.2, printStr p io "("]
    -- arguments
    show_method_args p c io decls.length 1 (decls.drop 1)
    let kwargs ← kwarg_decl r meth world
    if !kwargs.isEmpty then
      printStr p io "; "
      show_method_kwargs p c io (kwargs.getLastD "") kwargs
    printStr p io ")"
    show_method_params p a r.ofTV c.showTV io tv
  if !print_signature_only then
    if !(← assertBool a (getIO p io "compact" false)) then -- single-line mode
      printStr p io "\n"
      digit_align_width := JInt.wrap .i64 (digit_align_width.val + 4)
    -- module & file, re-using function from errorshow.jl
    c.print_module_path_file io (r.parentmodule meth) file line modulecolor digit_align_width

/--
Julia source: base/methodshow.jl:235-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# default compact view
show(io::IO, m::Method; kwargs...) = show_method(IOContext(io, :compact=>true), m; kwargs...)

```
-/
def show_Method [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (meth : Meth) : m Unit := do
  let io' ← withBool p a io "compact" true
  show_method (Ex := Ex) p a r c world io' meth

/--
Julia source: base/methodshow.jl:238-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/plain", m::Method; kwargs...) = show_method(io, m; kwargs...)

```
-/
def show_textplain_Method [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (meth : Meth) : m Unit :=
  show_method (Ex := Ex) p a r c world io meth

/--
Julia source: base/methodshow.jl:287-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_method_list_header(io::IO, ms::MethodList, namefmt::Function)
    tn = ms.tn
    name = tn.singletonname
    hasname = isdefined(tn.module, name) &&
              typeof(getfield(tn.module, name)) <: Function
    n = length(ms)
    m = n==1 ? "method" : "methods"
    print(io, "# $n $m")
    sname = string(name)
    namedisplay = namefmt(sname)
    if hasname
        what = (startswith(sname, '@') ?
                    "macro"
               : tn.module === Core && tn.wrapper <: Core.Builtin ?
                    "builtin function"
               : # else
                    "generic function")
        print(io, " for ", what, " ", namedisplay, " from ")

        col = get_stacktrace_color(parentmodule_before_main(tn.module))

        printstyled(io, tn.module, color=col)
    elseif '#' in sname
        print(io, " for anonymous function ", namedisplay)
    elseif iskindtype(tn.wrapper)
        print(io, " for type constructor")
    else
        print(io, " for callable object")
    end
    !iszero(n) && print(io, ":")
end

```
-/
def show_method_list_header (p : IOPrims m Io V) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (io : JIO Io V) (ms : ML) (namefmt : String → String) : m Unit := do
  let tn := r.tn ms
  let name := r.singletonname tn
  let hasname ← r.hasFunctionBinding (r.tnModule tn) name
  let n := (r.methods ms).length
  let mstr := if n == 1 then "method" else "methods"
  printStr p io ("# " ++ toString n ++ " " ++ mstr)
  let sname := name
  let namedisplay := namefmt sname
  if hasname then
    let what ← if sname.startsWith "@" then
        pure "macro"
      else if ← (if r.isCore (r.tnModule tn) then r.wrapperIsBuiltin tn else pure false) then
        pure "builtin function"
      else -- else
        pure "generic function"
    printAll p io [printStr p io " for ", printStr p io what, printStr p io " ", printStr p io namedisplay,
      printStr p io " from "]
    let col ← c.get_stacktrace_color (← c.parentmodule_before_main (r.tnModule tn))
    c.printstyled_color io [fun io => c.printModule io (r.tnModule tn)] col
  else if sname.toList.contains '#' then
    printAll p io [printStr p io " for anonymous function ", printStr p io namedisplay]
  else if r.wrapperIsKind tn then
    printStr p io " for type constructor"
  else
    printStr p io " for callable object"
  if n != 0 then printStr p io ":"

/--
Julia source: base/methodshow.jl:319-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Determine the `modulecolor` value to pass to `show_method`
function _modulecolor(method::Method)
    mmt = get_methodtable(method)
    # TODO: this looks like a buggy bit of internal hacking, so disable for now
    return nothing
    if mmt === nothing || mmt.module === parentmodule(method)
        return nothing
    end
    # `mmt` is only particularly relevant for external method tables. Since the primary
    # method table is shared, we now need to distinguish "primary" methods by trying to
    # check if there is a primary `DataType` to identify it with. c.f. how `jl_method_def`
    # would derive this same information (for the name).
    ft = argument_datatypename((unwrap_unionall(method.sig)::DataType).parameters[1])
    if ft === nothing || parentmodule(method) === ft.module !== Core
        return nothing
    end
    m = parentmodule_before_main(method)
    return get_stacktrace_color(m)
end

```
-/
def _modulecolor (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (meth : Meth) : m (Option Col) := do
  let _mmt ← r.get_methodtable meth
  -- TODO: this looks like a buggy bit of internal hacking, so disable for now
  return none
  -- (the rest of the method body follows the `return` and never runs)

/-- `lpad(s, n)` of an ASCII string: spaces before `s` up to `n` characters. -/
def lpadAscii (s : String) (n : Int) : String :=
  String.ofList (List.replicate (n - s.length).toNat ' ') ++ s

/-- The `for meth in ms` loop of `show_method_table`: `(n, rest, last)`. -/
def show_method_table_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (max : JInt64)
    (digit_align_width : Nat) (last_shown_line_infos : Option V) (n rest : Int) (last : Option Meth) :
    List Meth → m (Int × Int × Option Meth)
  | [] => pure (n, rest, last)
  | meth :: ms => do
    if max.val == -1 || n < max.val then
      let n := n + 1
      printStr p io "\n"
      printStr p io (" " ++ lpadAscii ("[" ++ toString n ++ "]") (digit_align_width + 2) ++ " ")
      show_method (Ex := Ex) p a r c world io meth (← _modulecolor r meth)
      let (file, line) ← updated_methodloc (Ex := Ex) c r meth
      if let some v := last_shown_line_infos then
        c.push_line_info v (file, line)
      show_method_table_loop p a r c world io max digit_align_width last_shown_line_infos n rest last ms
    else
      show_method_table_loop p a r c world io max digit_align_width last_shown_line_infos n (rest + 1) (some meth) ms

/--
Julia source: base/methodshow.jl:339-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_method_table(io::IO, ms::MethodList, max::Int=-1, header::Bool=true)
    tn = ms.tn
    name = tn.singletonname
    hasname = isdefined(tn.module, name) &&
              typeof(getfield(tn.module, name)) <: Function
    if header
        show_method_list_header(io, ms, str -> "\""*str*"\"")
    end
    n = rest = 0
    last = nothing

    last_shown_line_infos = get(io, :last_shown_line_infos, nothing)
    last_shown_line_infos === nothing || empty!(last_shown_line_infos)

    digit_align_width = length(string(max > 0 ? max : length(ms)))

    for meth in ms
        if max == -1 || n < max
            n += 1
            println(io)

            print(io, " ", lpad("[$n]", digit_align_width + 2), " ")

            show_method(io, meth; modulecolor=_modulecolor(meth))

            file, line = updated_methodloc(meth)
            if last_shown_line_infos !== nothing
                push!(last_shown_line_infos, (string(file), line))
            end
        else
            rest += 1
            last = meth
        end
    end
    if rest > 0
        println(io)
        if rest == 1 && last isa Method
            show_method(io, last)
        else
            print(io, "... $rest methods not shown")
            if hasname
                print(io, " (use methods($name) to see them all)")
            end
        end
    end
    nothing
end

```
-/
def show_method_table [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (ms : ML)
    (max : JInt64 := JInt.wrap .i64 (-1)) (header : Bool := true) : m Unit := do
  let tn := r.tn ms
  let name := r.singletonname tn
  let hasname ← r.hasFunctionBinding (r.tnModule tn) name
  if header then
    show_method_list_header p r c io ms (fun str => "\"" ++ str ++ "\"")
  let last_shown_line_infos := match getIO p io "last_shown_line_infos" () with
    | .inl v => some v
    | .inr () => none
  if let some v := last_shown_line_infos then c.empty_line_infos v
  let digit_align_width := (toString (if max.val > 0 then max.val else (r.methods ms).length)).length
  let (_, rest, last) ← show_method_table_loop (Ex := Ex) p a r c world io max digit_align_width last_shown_line_infos 0 0 none
    (r.methods ms)
  if rest > 0 then
    printStr p io "\n"
    match rest == 1, last with
    | true, some last => show_method (Ex := Ex) p a r c world io last
    | _, _ =>
      printStr p io ("... " ++ toString rest ++ " methods not shown")
      if hasname then
        printAll p io [printStr p io " (use methods(", print_Symbol p io name, printStr p io ") to see them all)"]

/--
Julia source: base/methodshow.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ms::MethodList) = show_method_table(io, ms)
```
-/
def show_MethodList [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (ms : ML) : m Unit :=
  show_method_table (Ex := Ex) p a r c world io ms

/--
Julia source: base/methodshow.jl:388-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/plain", ms::MethodList) = show_method_table(io, ms)
```
-/
def show_textplain_MethodList [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (ms : ML) : m Unit :=
  show_method_table (Ex := Ex) p a r c world io ms

/--
Julia source: base/methodshow.jl:389-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, mt::Core.MethodTable) = print(io, mt.module, ".", mt.name, " is a Core.MethodTable with ", length(mt), " methods.")

```
-/
def show_MethodTable (p : IOPrims m Io V) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (io : JIO Io V) (mt : MT) : m Unit :=
  printAll p io [c.printModule io (r.mtModule mt), printStr p io ".", print_Symbol p io (r.mtName mt),
    printStr p io " is a Core.MethodTable with ", printIntS p io (r.mtLength mt), printStr p io " methods."]

/--
Julia source: base/methodshow.jl:391-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function inbase(m::Module)
    if m == Base
        true
    else
        parent = parentmodule(m)
        parent === m ? false : inbase(parent)
    end
end
```
-/
def inbase [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (mod : Mod) : m Bool := do
  if r.isBase mod then
    return true
  else
    let parent ← pure (r.parentmoduleMod mod)
    if r.egalMod parent mod then return false else inbase r parent
partial_fixpoint

/--
Julia source: base/methodshow.jl:399-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fileurl(file) = let f = find_source_file(file); f === nothing ? "" : "file://"*f; end

```
-/
def fileurl (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (file : Bytes) : m Bytes := do
  let f ← c.find_source_file file
  return match f with
    | none => []
    | some f => lit "file://" ++ f

/-- `occursin(r"In\[[0-9]+\]"a, file)` on the bytes of `file` (the pattern is ASCII). -/
def occursInBracket (file : Bytes) : Bool :=
  let rec go : List UInt8 → Bool
    | 73 :: 110 :: 91 :: rest =>
      let ds := rest.takeWhile (fun c => 48 ≤ c && c ≤ 57)
      (!ds.isEmpty && (rest.drop ds.length).head? == some 93) || go (110 :: 91 :: rest)
    | _ :: rest => go rest
    | [] => false
  go file

/-- `s[k:end]` of a `String` (string.jl:579-596, `getindex(s::String, r::UnitRange{Int})`) at the
range `k:lastindex(s)`: the installed `stringGetindexRange` over the bytes of `s`, with
`checkbounds(s, r)` of basic.jl:206 (`isempty(r) || (checkbounds(Bool, s, first(r)) &&
checkbounds(Bool, s, last(r)))`) and the installed `String` pointer convention (every `String`'s
data starts at offset 0 of its own bytes, so `pointer(s, i)` is the offset `i - 1` into `s`). Its
`BoundsError` and `StringIndexError` are show.jl's; allocating at most `ncodeunits(s)` bytes cannot
fail, so no other error arises. -/
def sliceFrom (s : Bytes) (k : Nat) : m Bytes := do
  let liftS {α : Type} : JuliaLean.Strings.SJl α → m α := fun
    | .ok a => pure a
    | .error (.jl e) => throwShow (.jl e)
    | .error (.stringIndexError _) => throwShow .stringIndexError
    | .error _ => throwShow (.errorException "unreachable: String range getindex")
  if h : s.length < 2 ^ 62 then
    let js : JuliaLean.Strings.JStr := ⟨s, h⟩
    let j ← liftS (JuliaLean.base.strings.string.lastindexString JuliaLean.base.strings.string.stringNcodeunits JuliaLean.base.strings.string.stringBetweenIndex JuliaLean.base.strings.string.stringBetweenByte JuliaLean.base.strings.string.stringCodeunitAt js)
    let checkbounds (t : JuliaLean.Strings.JStr) (a b : JuliaLean.base.strings.string.Index) :
        JuliaLean.Strings.SJl Unit :=
      if b.val < a.val || (1 ≤ a.val && a.val ≤ t.bytes.length && 1 ≤ b.val && b.val ≤ t.bytes.length)
      then .ok () else .error (.jl .boundsError)
    let alloc (n : Nat) : JuliaLean.Strings.SJl JuliaLean.Strings.JStr :=
      if hn : (List.replicate n (0 : UInt8)).length < 2 ^ 62 then .ok ⟨_, hn⟩ else .error .outOfMemory
    let copy (_dest src : Int) (n : Nat) (_ss : JuliaLean.Strings.JStr) : JuliaLean.Strings.JStr :=
      let b := (s.drop src.toNat).take n
      if hb : b.length < 2 ^ 62 then ⟨b, hb⟩ else js
    let r ← liftS (JuliaLean.base.strings.string.stringGetindexRange (fun a b => decide (b.val < a.val)) checkbounds
      (fun n => .ok n.val.toNat) alloc (·.val) (fun _ _ f => f ()) copy js (JuliaLean.Strings.ix k) j)
    return r.bytes
  else throwShow (.errorException "unreachable: a String has fewer than 2^62 bytes")

/-- `length(s)` of a `String`: the installed string.jl model `length(s::String)` (string.jl:598-600)
over the bytes of `s`. -/
def lengthB (s : Bytes) : Nat :=
  (JuliaLean.base.strings.string.lengthView (fun (s : Bytes) => JInt.wrap .i64 s.length)
    (fun s i => s.getD (i.val - 1).toNat 0) s).val.toNat


/-- The `LibGit2.with(…) do repo … end` part of `url`: `with(f, x)` runs `f(x)` and closes `x`,
also on an exception. -/
def libgit2_url {Repo Cfg : Type} (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (g : LibGit2Ops m Repo Cfg)
    (file : Bytes) (line : JInt .i32) : m Bytes := do
  let d := c.paths.dirname file
  let repo ← g.GitRepoExt d
  let res ← tryCatchThe Ex (do
      let cfg ← g.GitConfig repo
      let res ← tryCatchThe Ex (do
          let u ← g.get cfg (lit "remote.origin.url") []
          let u ← g.githubCapture u
          let commit ← g.head_oid repo
          let root ← g.path repo
          if file.take root.length == root || (← g.realpath file).take root.length == root then
            -- `file[length(root)+1:end]`: a character count used as a byte index
            pure (lit "https://github.com/" ++ u ++ lit "/tree/" ++ commit ++ lit "/" ++
              (← sliceFrom file (lengthB root + 1)) ++ lit "#L" ++ lit (decStr line))
          else
            fileurl c file)
        (fun e => do g.closeCfg cfg; throwThe Ex e)
      g.closeCfg cfg
      pure res)
    (fun e => do g.closeRepo repo; throwThe Ex e)
  g.closeRepo repo
  return res

/--
Julia source: base/methodshow.jl:401-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function url(m::Method)
    M = parentmodule(m)
    (m.file === :null || m.file === :string) && return ""
    file = string(m.file)
    line = m.line
    line <= 0 || occursin(r"In\[[0-9]+\]"a, file) && return ""
    Sys.iswindows() && (file = replace(file, '\\' => '/'))
    if inbase(M)
        if isempty(Base.GIT_VERSION_INFO.commit)
            # this url will only work if we're on a tagged release
            return "https://github.com/JuliaLang/julia/tree/v$VERSION/base/$file#L$line"
        else
            return "https://github.com/JuliaLang/julia/tree/$(Base.GIT_VERSION_INFO.commit)/base/$file#L$line"
        end
    end
    libgit2_id = PkgId(UUID((0x76f85450_5226_5b5a,0x8eaa_529ad045b433)), "LibGit2")
    LibGit2 = maybe_root_module(libgit2_id)
    if LibGit2 isa Module
        try
            d = dirname(file)
            return let file = file
                LibGit2.with(LibGit2.GitRepoExt(d)) do repo
                    LibGit2.with(LibGit2.GitConfig(repo)) do cfg
                        u = LibGit2.get(cfg, "remote.origin.url", "")
                        u = (match(LibGit2.GITHUB_REGEX,u)::AbstractMatch).captures[1]
                        commit = string(LibGit2.head_oid(repo))
                        root = LibGit2.path(repo)
                        if startswith(file, root) || startswith(realpath(file), root)
                            "https://github.com/$u/tree/$commit/"*file[length(root)+1:end]*"#L$line"
                        else
                            fileurl(file)
                        end
                    end
                end
            end::String
        catch
            # oops, this was a bad idea
        end
    end
    return fileurl(file)
end

```
-/
def url [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI) (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (meth : Meth) :
    m Bytes := do
  let M := r.parentmodule meth
  if r.file meth == "null" || r.file meth == "string" then return []
  let mut file := lit (r.file meth)
  let line := r.line meth
  -- `line <= 0 || occursin(…) && return ""` parses as `line <= 0 || (occursin(…) && return "")`
  if !(line.val ≤ 0) && occursInBracket file then return []
  if c.iswindows then file := file.map (fun b => if b == 92 then 47 else b)
  if ← inbase r M then
    if c.git_commit.isEmpty then
      -- this url will only work if we're on a tagged release
      return lit "https://github.com/JuliaLang/julia/tree/v" ++ c.version ++ lit "/base/" ++ file ++ lit "#L" ++ lit (decStr line)
    else
      return lit "https://github.com/JuliaLang/julia/tree/" ++ c.git_commit ++ lit "/base/" ++ file ++ lit "#L" ++ lit (decStr line)
  if let some ⟨_, _, g⟩ := c.libgit2 then
    let res ← tryCatchThe Ex (some <$> libgit2_url (Ex := Ex) c g file line)
      (fun _ => pure none) -- oops, this was a bad idea
    if let some u := res then return u
  fileurl c file

/-- `String[isempty(d[2]) ? string(d[1]) : string(d[1], "::<b>", d[2], "</b>") for d in decls[2:end]]`. -/
def htmlArgs (decls : List (Bytes × Bytes)) : List Bytes :=
  (decls.drop 1).map fun d => if d.2.isEmpty then d.1 else d.1 ++ lit "::<b>" ++ d.2 ++ lit "</b>"

/-- `join(io, strings, ", ", ", ")`. -/
def joinIO (p : IOPrims m Io V) (io : JIO Io V) (delim : String) : List Bytes → m Unit
  | [] => pure ()
  | [x] => printBytes p io x
  | x :: xs => do
    printBytes p io x
    printStr p io delim
    joinIO p io delim xs

/--
Julia source: base/methodshow.jl:443-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/html", m::Method)
    tv, decls, _file, line = arg_decl_parts(m, true)
    sig = unwrap_unionall(m.sig)
    if sig <: Tuple{Core.Builtin, Vararg}
        print(io, m.name, "(...) in ", parentmodule(m))
        return
    end
    print(io, decls[1][2], "(")
    join(
        io,
        String[
            isempty(d[2]) ? string(d[1]) : string(d[1], "::<b>", d[2] , "</b>") for d in decls[2:end]
        ],
        ", ",
        ", ",
    )
    kwargs = kwarg_decl(m)
    if !isempty(kwargs)
        print(io, "; <i>")
        join(io, map(sym_to_string, kwargs), ", ", ", ")
        print(io, "</i>")
    end
    print(io, ")")
    if !isempty(tv)
        print(io,"<i>")
        show_method_params(io, tv)
        print(io,"</i>")
    end
    print(io, " in ", parentmodule(m))
    if line > 0
        file, line = updated_methodloc(m)
        u = url(m)
        if isempty(u)
            print(io, " at ", file, ":", line)
        else
            print(io, """ at <a href="$u" target="_blank">""",
                  file, ":", line, "</a>")
        end
    end
end

```
-/
def show_html_Method [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (meth : Meth) : m Unit := do
  let (tv, decls, _file, line) ← arg_decl_parts (Ex := Ex) r c meth true
  let sig := r.unwrap_unionall (r.sig meth)
  if ← r.isBuiltinSig sig then
    printAll p io [print_Symbol p io (r.name meth), printStr p io "(...) in ", c.printModule io (r.parentmodule meth)]
    return
  let d1 ← idx decls 1
  printAll p io [printBytes p io d1.2, printStr p io "("]
  joinIO p io ", " (htmlArgs decls)
  let kwargs ← kwarg_decl r meth world
  if !kwargs.isEmpty then
    printStr p io "; <i>"
    joinIO p io ", " (← kwargs.mapM (sym_to_string c))
    printStr p io "</i>"
  printStr p io ")"
  if !tv.isEmpty then
    printStr p io "<i>"
    show_method_params p a r.ofTV c.showTV io tv
    printStr p io "</i>"
  printAll p io [printStr p io " in ", c.printModule io (r.parentmodule meth)]
  if line.val > 0 then
    let (file, line) ← updated_methodloc (Ex := Ex) c r meth
    let u ← url (Ex := Ex) r c meth
    if u.isEmpty then
      printAll p io [printStr p io " at ", printBytes p io file, printStr p io ":", printIntS p io line]
    else
      printAll p io [printBytes p io (lit " at <a href=\"" ++ u ++ lit "\" target=\"_blank\">"),
        printBytes p io file, printStr p io ":", printIntS p io line, printStr p io "</a>"]

/-- The `for meth in ms` loop of `show(io, ::MIME"text/html", ms::MethodList)`. -/
def show_html_methods [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (close : String) : List Meth → m Unit
  | [] => pure ()
  | meth :: ms => do
    printStr p io "<li> "
    show_html_Method (Ex := Ex) p a r c world io meth
    printStr p io close
    show_html_methods p a r c world io close ms

/--
Julia source: base/methodshow.jl:484-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, mime::MIME"text/html", ms::MethodList)
    show_method_list_header(io, ms, str -> "<b>"*str*"</b>")
    print(io, "<ul>")
    for meth in ms
        print(io, "<li> ")
        show(io, mime, meth)
        print(io, "</li> ")
    end
    print(io, "</ul>")
end

```
-/
def show_html_MethodList [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (ms : ML) : m Unit := do
  show_method_list_header p r c io ms (fun str => "<b>" ++ str ++ "</b>")
  printStr p io "<ul>"
  show_html_methods (Ex := Ex) p a r c world io "</li> " (r.methods ms)
  printStr p io "</ul>"

/-- The `for (i, m) in enumerate(mt)` loop of `show(io, ::MIME"text/plain", mt::AbstractVector{Method})`. -/
def show_textplain_vector_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (last_shown_line_infos : Option V)
    (first : Bool) (i : Nat) : List Meth → m Bool
  | [] => pure first
  | meth :: ms => do
    if !first then printStr p io "\n"
    printStr p io ("[" ++ toString i ++ "] ")
    show_Method (Ex := Ex) p a r c world io meth
    let (file, line) ← updated_methodloc (Ex := Ex) c r meth
    if let some v := last_shown_line_infos then
      c.push_line_info v (file, line)
    show_textplain_vector_loop p a r c world io last_shown_line_infos false (i + 1) ms

/--
Julia source: base/methodshow.jl:495-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# pretty-printing of AbstractVector{Method}
function show(io::IO, mime::MIME"text/plain", mt::AbstractVector{Method})
    last_shown_line_infos = get(io, :last_shown_line_infos, nothing)
    last_shown_line_infos === nothing || empty!(last_shown_line_infos)
    first = true
    for (i, m) in enumerate(mt)
        first || println(io)
        first = false
        print(io, "[$(i)] ")
        show(io, m)
        file, line = updated_methodloc(m)
        if last_shown_line_infos !== nothing
            push!(last_shown_line_infos, (string(file), line))
        end
    end
    first && summary(io, mt)
    nothing
end

```
-/
def show_textplain_MethodVector [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (mt : List Meth) : m Unit := do
  let last_shown_line_infos := match getIO p io "last_shown_line_infos" () with
    | .inl v => some v
    | .inr () => none
  if let some v := last_shown_line_infos then c.empty_line_infos v
  let first ← show_textplain_vector_loop (Ex := Ex) p a r c world io last_shown_line_infos true 1 mt
  if first then c.summary io mt

/--
Julia source: base/methodshow.jl:514-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, mime::MIME"text/html", mt::AbstractVector{Method})
    summary(io, mt)
    if !isempty(mt)
        print(io, ":<ul>")
        for d in mt
            print(io, "<li> ")
            show(io, mime, d)
        end
        print(io, "</ul>")
    end
    nothing
end
```
-/
def show_html_MethodVector [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V) (a : AnyOps V Ty) (r : Reflect m V Ty Meth Mod TV VN TN ML MT MI)
    (c : Callees m Io V Ty Meth Mod TV VN Col Fn) (world : JInt .u64) (io : JIO Io V) (mt : List Meth) : m Unit := do
  c.summary io mt
  if !mt.isEmpty then
    printStr p io ":<ul>"
    show_html_methods (Ex := Ex) p a r c world io "" mt
    printStr p io "</ul>"

end

end JuliaLean.base.methodshow


namespace JuliaLean.ErrorShow


structure MethodView where
  functionName : String
  arguments : List String
  keywords : List String := []
  whereParameters : List String := []
  location : String
  deriving Repr, DecidableEq

def methodSignature (method : MethodView) : String :=
  let positional := String.intercalate ", " method.arguments
  let keywordText := if method.keywords.isEmpty then ""
    else "; " ++ String.intercalate ", " method.keywords
  let whereText := if method.whereParameters.isEmpty then ""
    else " where {" ++ String.intercalate ", " method.whereParameters ++ "}"
  method.functionName ++ "(" ++ positional ++ keywordText ++ ")" ++ whereText

/-- `show(::Method)` and `show(::MIME\"text/plain\", ::Method)`,
`base/methodshow.jl:235-284`. The location is already rendered by
`print_module_path_file`. -/
def showMethod (method : MethodView) (compact signatureOnly : Bool) : String :=
  let signature := methodSignature method
  if signatureOnly then signature
  else if compact then signature ++ " " ++ method.location
  else signature ++ "\n    " ++ method.location

end JuliaLean.ErrorShow

namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

/-! ### `base/methodshow.jl` -/

inductive SymbolForm where
  | self
  | unused
  | generated (base : String)
  | plain (name : String)
  deriving Repr, DecidableEq

def stripGensym : SymbolForm → String
  | .self | .unused => ""
  | .generated base | .plain base => base

inductive VarargForm where
  | ordinary
  | unbounded
  | fixed (count : Nat)
  deriving Repr, DecidableEq

def argumentDeclaration (name typeText : String) (isAny : Bool)
    (vararg : VarargForm) : String × String :=
  let name := stripGensym (.plain name)
  match vararg with
  | .ordinary => if isAny then (name, "") else (name, typeText)
  | .unbounded => if isAny then (name ++ "...", "") else (name, typeText ++ "...")
  | .fixed count => (name, "Vararg{" ++ typeText ++ ", " ++ toString count ++ "}")

def methodArgumentNames (slotNames : List String) (argumentCount : Nat) : List String :=
  if slotNames.isEmpty then [] else slotNames.take argumentCount

def argumentDeclarationParts (arguments : List (String × String)) : List (String × String) :=
  arguments

def moveSplatLast (keywords : List String) : List String :=
  match keywords.find? (fun name => name.endsWith "...") with
  | none => keywords
  | some splat => (keywords.erase splat) ++ [splat]

def keywordDeclarations (slotNames : List String) : List String :=
  let filtered := slotNames.filter fun name => !name.isEmpty && !name.contains '#'
  if filtered.isEmpty then ["..."] else moveSplatLast filtered

def showWhereParameters : List String → String
  | [] => ""
  | [parameter] => " where " ++ parameter
  | parameters => " where {" ++ String.intercalate ", " parameters ++ "}"

def symbolToString (empty generated : Bool) (shown : String) : String :=
  if empty then "..." else if generated then shown ++ "..." else shown

inductive FunctionLocation where
  | location (file : String) (line : Int)
  | noDefinitions
  | multipleDefinitions
  | notCallable
  deriving Repr, DecidableEq

def singleFunctionLocation (callable : Bool) (locations : List (String × Int)) : FunctionLocation :=
  match locations with
  | [] => if callable then .noDefinitions else .notCallable
  | [(file, line)] => .location file line
  | _ => .multipleDefinitions

def fixupStdlibPath (buildPathDiff compilerSource : Bool)
    (stdlibPath compilerPath path : String) : String :=
  if compilerSource then compilerPath else if buildPathDiff then stdlibPath else path

def updatedMethodLocation (original : String × Int)
    (callback : Option (String × Int)) : String × Int :=
  callback.getD original

def methodListHeader (count : Nat) (kind name moduleName : String) : String :=
  s!"# {count} {if count = 1 then "method" else "methods"} for {kind} {name} from {moduleName}" ++
    (if count = 0 then "" else ":")

def methodTableRows (rows : List String) (maximum : Int) : List String :=
  if maximum < 0 then rows else rows.take maximum.toNat

def moduleColor : Option String := none

def renderMethodContainer (header : String) (rows : List String)
    (html : Bool) : String :=
  if html then header ++ "<ul>" ++ String.intercalate "" (rows.map fun row => "<li> " ++ row ++ "</li> ") ++ "</ul>"
  else header ++ String.intercalate "\n" rows

def inBase (parents : List String) : Bool := parents.contains "Base"

inductive MethodUrl where
  | none
  | github (commit file : String) (line : Int)
  | localFile (file : String) (line : Int)
  deriving Repr, DecidableEq

def methodUrl (validLocation inBaseModule hasCommit : Bool)
    (commit file : String) (line : Int) : MethodUrl :=
  if !validLocation then .none
  else if inBaseModule then .github (if hasCommit then commit else "tag") file line
  else .localFile file line

end JuliaLean.ErrorShow.Coverage


namespace JuliaLean.ErrorShow.MethodshowFaithful

open JuliaLean.ErrorShow.Coverage

abbrev R (α : Type) := Except String α

inductive SymbolClass where | self | unused | generated (base : String) | plain (name : String) deriving Repr, DecidableEq

def stripGensym : SymbolClass → String
  | .self | .unused => ""
  | .generated base | .plain base => base

inductive ArgType where | any | ordinary (text : String) | unboundedVararg (text : String) | fixedVararg (text : String) (count : Nat) deriving Repr, DecidableEq

def argtypeDecl (name : SymbolClass) : ArgType → String × String
  | .any => (stripGensym name, "")
  | .ordinary text => (stripGensym name, text)
  | .unboundedVararg "Any" => (stripGensym name ++ "...", "")
  | .unboundedVararg text => (stripGensym name, text ++ "...")
  | .fixedVararg text count => (stripGensym name, "Vararg{" ++ text ++ ", " ++ toString count ++ "}")

def methodArgnames (uncompressed : List String) (nargs : Nat) : List String :=
  if uncompressed.isEmpty then [] else uncompressed.take nargs

structure ArgDeclParts where
  typevars : List String
  declarations : List (String × String)
  file : String
  line : Int
  deriving Repr, DecidableEq

def argDeclParts (typevars : List String) (argnames : List SymbolClass) (argtypes : List ArgType)
    (file : String) (line : Int) : ArgDeclParts :=
  let declarations := if argnames.length < argtypes.length then List.replicate argtypes.length ("", "")
    else (argnames.zip argtypes).map fun (name, type) => argtypeDecl name type
  { typevars, declarations, file, line }

def kwargDecl (eligible found : Bool) (slotnames : List String) : List String :=
  if !eligible || !found then [] else
    let filtered := slotnames.filter fun name => !name.isEmpty && !name.contains '#'
    let moved := match filtered.find? (·.endsWith "...") with
      | none => filtered | some splat => filtered.erase splat ++ [splat]
    if moved.isEmpty then ["..."] else moved

def showMethodParams : List String → String
  | [] => "" | [parameter] => " where " ++ parameter
  | parameters => " where {" ++ String.intercalate ", " parameters ++ "}"

def fixupStdlibPath (stdlibDiff compilerSource : Bool) (stdlib compiler original : String) : String :=
  if compilerSource then compiler else if stdlibDiff then stdlib else original

def updatedMethodloc (original callback : Option (String × Int)) : Option (String × Int) :=
  callback.orElse fun _ => original

def functionlocMethod (file : String) (line : Int) : R (String × Int) :=
  if line ≤ 0 then .error "could not determine location of method definition" else .ok (file, line)

def functionlocMethodInstance (file : String) (line : Int) := functionlocMethod file line

def functionlocFunctionTypes (selectedFile : String) (selectedLine : Int) :=
  functionlocMethod selectedFile selectedLine

def functionlocArgtypes (selectedFile : String) (selectedLine : Int) :=
  functionlocMethod selectedFile selectedLine

def functionlocSingle (callable : Bool) (methods : List (String × Int)) : R (String × Int) :=
  match methods with
  | [] => .error (if callable then "function has no definitions" else "object is not callable")
  | [method] => .ok method
  | _ => .error "function has multiple methods; please specify a type signature"

inductive SymbolText where | ellipsis | trailingDots (shownBase : String) | ordinary (shown : String) deriving Repr, DecidableEq

def symToString : SymbolText → String
  | .ellipsis => "..." | .trailingDots base => base ++ "..." | .ordinary shown => shown

def showMethodCompact (rendered : String) : String := rendered

def showMethodPlain (rendered : String) : String := rendered

structure MethodRender where
  functionName : String
  args : List (String × String)
  keywords : List String
  typevars : List String
  location : String
  deriving Repr, DecidableEq

def showMethod (method : MethodRender) (compact signatureOnly : Bool) : String :=
  let args := method.args.map fun (name, type) => name ++ if type.isEmpty then "" else "::" ++ type
  let keywords := if method.keywords.isEmpty then "" else "; " ++ String.intercalate ", " method.keywords
  let signature := method.functionName ++ "(" ++ String.intercalate ", " args ++ keywords ++ ")" ++ showMethodParams method.typevars
  if signatureOnly then signature else signature ++ (if compact then " " else "\n") ++ method.location

def showMethodCompactFaithful (method : MethodRender) : String := showMethod method true false

def showMethodPlainFaithful (method : MethodRender) : String := showMethod method false false

def methodListHeader (count : Nat) (kind name moduleName : String) : String :=
  "# " ++ toString count ++ " " ++ (if count = 1 then "method" else "methods") ++
    " for " ++ kind ++ " " ++ name ++ " from " ++ moduleName ++ if count = 0 then "" else ":"

def moduleColor (_method : String) : Option String := none

def showMethodTable (header : Option String) (methods : List String) (maximum : Int) : String :=
  let shown := if maximum < 0 then methods else methods.take maximum.toNat
  let rest := methods.length - shown.length
  header.getD "" ++ String.intercalate "\n" (shown.zipIdx.map fun (method, i) => s!" [{i+1}] {method}") ++
    (if rest = 0 then "" else "\n... " ++ toString rest ++ " methods not shown")

def showMethodList (table : String) : String := table

def showMethodListPlain (table : String) : String := table

def showCoreMethodTable (moduleName methodName : String) (count : Nat) : String :=
  moduleName ++ "." ++ methodName ++ " is a Core.MethodTable with " ++ toString count ++ " methods."

def inBase : List String → Bool
  | [] => false | moduleName :: parents => "Base" == moduleName || inBase parents

def fileUrl (resolved : Option String) : String := resolved.getD ""

inductive UrlCase where | invalid | baseTagged (version file : String) (line : Int) | baseCommit (commit file : String) (line : Int) | package (url : String) | local (file : String) deriving Repr, DecidableEq

def methodUrl : UrlCase → String
  | .invalid => "" | .baseTagged version file line => s!"https://github.com/JuliaLang/julia/tree/v{version}/base/{file}#L{line}"
  | .baseCommit commit file line => s!"https://github.com/JuliaLang/julia/tree/{commit}/base/{file}#L{line}"
  | .package url => url | .local file => "file://" ++ file

def showMethodHtml (signature moduleName location : String) (url : Option String) : String :=
  signature ++ " in " ++ moduleName ++ match url with | none => location | some href => " at <a href=\"" ++ href ++ "\" target=\"_blank\">" ++ location ++ "</a>"

def showMethodListHtml (header : String) (methods : List String) : String :=
  header ++ "<ul>" ++ String.intercalate "" (methods.map fun method => "<li> " ++ method ++ "</li> ") ++ "</ul>"

def showMethodVectorPlain (summary : String) (methods : List String) : String :=
  if methods.isEmpty then summary else String.intercalate "\n" (methods.zipIdx.map fun (method, i) => s!"[{i+1}] {method}")

def showMethodVectorHtml (summary : String) (methods : List String) : String :=
  summary ++ if methods.isEmpty then "" else ":<ul>" ++ String.intercalate "" (methods.map fun method => "<li> " ++ method ++ "</li>") ++ "</ul>"

end JuliaLean.ErrorShow.MethodshowFaithful
