import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.expr
import JuliaLean.base.version
import JuliaLean.base.strings.substring

/-!
# Model of `base/deprecated.jl`

The deprecation machinery and deprecated methods of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

* `depwarn`, `_depwarn` and `firstcaller` run in the mutable world of `JuliaLean.base.io.M`. The
  runtime options, backtraces, stack-frame lookup and the `@logmsg` logging machinery are typed
  operations of `DepOps` with no assumed laws. `@logmsg` receives the action computing its keyword
  arguments, so the backtrace walk runs only when the logger keeps the message.
* The macros (`@deprecate`, `@deprecate_binding`, `@deprecate_stdlib`, `@deprecate_moved`,
  `@get!`, `@pure`) are functions on the installed `base/expr.jl` syntax model returning the
  expansion. A `quote` of this file is the `Expr` the parser builds, with a `LineNumberNode` for
  each statement line; Base records this file as `deprecated.jl`. Printing a value (`string`,
  `sprint(show_unquoted, x)`) and `Base.root_module` are typed operations of `MacroOps`.
* Each method that a top-level `@deprecate old new` defines is a Lean function: `depwarn` with the
  message and function name that `@deprecate` computes for it (both as printed by Julia), then
  the replacement call. Replacement callees defined in other files are parameters.
-/

namespace JuliaLean.base.deprecated

open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.expr (Value LeafOps ExprError Sym esc i64)
open JuliaLean.base.version (VersionNumber VersionIdentifier VersionRegexOps versionLess)

/-- The `funcsym` argument of `depwarn`: `nothing`, a `Symbol`, or a collection of `Symbol`s. -/
inductive FuncSym where
  | nothing
  | sym (name : Sym)
  | syms (names : List Sym)

/-- The two log levels `_depwarn` uses. -/
inductive LogLevel where
  /-- `CoreLogging.Warn`. -/
  | warn
  /-- `CoreLogging.BelowMinLevel`. -/
  | belowMinLevel

/-- `lkup.linfo` of a stack frame: a `MethodInstance` whose `def` is a `Method` (with its name and
module) or a `Module`, or a value that is not a `MethodInstance`. -/
inductive Linfo (Mod : Type) where
  | method (name : Sym) (module : Mod)
  | module (m : Mod)
  | other

/-- The keyword arguments `_depwarn` passes to `@logmsg`. -/
structure DepwarnLog (Ip Frame Mod : Type) where
  _module : Mod
  _file : String
  _line : JInt64
  _id : Ip × FuncSym
  _group : Sym
  caller : Frame
  maxlog : Option JInt64

/-- The runtime that `depwarn` uses: instruction pointers `Ip`, stack frames `Frame` and modules
`Mod`. -/
structure DepOps (World Ip Frame Mod : Type) where
  /-- `JLOptions().depwarn`. -/
  optDepwarn : M World (JInt .i8)
  backtrace : M World (List Ip)
  /-- `StackTraces.lookup(ip)`. -/
  lookup : Ip → M World (List Frame)
  /-- `StackTraces.UNKNOWN`. -/
  unknown : Frame
  /-- `==` on stack frames. -/
  frameEq : Frame → Frame → M World Bool
  fromC : Frame → Bool
  func : Frame → Sym
  linfo : Frame → Linfo Mod
  file : Frame → Sym
  line : Frame → JInt64
  /-- `C_NULL`, equal to `Ptr{Cvoid}(0)`. -/
  cNull : Ip
  /-- The module `Core`. -/
  core : Mod
  /-- `@logmsg(level, msg, kwargs...)`; the logging machinery runs the given action to compute
  the keyword arguments only for a message it does not filter out. -/
  logmsg : LogLevel → String → M World (DepwarnLog Ip Frame Mod) → M World Unit
  /-- `ccall(:jl_is_in_pure_context, Bool, ())`. -/
  isInPureContext : M World Bool

/-- Exceptions thrown by the macros. -/
inductive MacroError (L : Type) where
  | expr (e : ExprError)
  /-- `FieldError(typeof(x), field)` of reading a field `x` does not have. -/
  | fieldError (x : Value L) (field : Sym)

abbrev MacroResult (L α : Type) := Except (MacroError L) α

/-- Base methods the macros apply to syntax values. -/
structure MacroOps (L : Type) where
  lo : LeafOps L
  /-- A `String` value. -/
  ofString : String → L
  /-- `string(x)`, as used by string interpolation. -/
  string : Value L → String
  /-- `sprint(show_unquoted, x)`. -/
  showUnquoted : Value L → String
  /-- The `debuginfo` reset that `remove_linenums!` applies to a `CodeInfo`. -/
  codeInfoNoLines : L → L
  /-- `Base.root_module(Base, mod)`. -/
  rootModule : Value L → MacroResult L L

/-- Operations of the deprecated `SubString{T}(s, i, j, Val(:noshift))` constructors on a
string `s` of type `S`, producing a `SubString` of type `SS`. -/
structure SubStringOps (World S SS : Type) where
  prevind : S → JInt64 → M World JInt64
  /-- `@inbounds isvalid(s, i)`. -/
  isvalid : S → JInt64 → M World Bool
  /-- `string_index_err(s, i)`, which throws. -/
  string_index_err : S → JInt64 → M World Unit
  /-- `@inbounds raw_substring(s, i, j)`. -/
  raw_substring : S → JInt64 → JInt64 → M World SS

/-- The type operations of `tuple_type_cons`. -/
structure TupleTypeOps (World Ty : Type) where
  /-- `T === Union{}`. -/
  isBottom : Ty → Bool
  /-- `T <: Tuple`. -/
  isTupleType : Ty → Bool
  /-- `T.parameters`. -/
  parameters : Ty → M World (List Ty)
  /-- `Tuple{params...}`. -/
  tupleOf : List Ty → M World Ty
  /-- `Union{}`. -/
  bottom : Ty

/-- The operations the deprecated `Type{...}` property methods use, for a type value `X` and
property values `V`. -/
structure TypePropertyOps (World X V : Type) where
  /-- `Core.svec(type_parameter(x))`. -/
  svecTypeParameter : X → M World V
  /-- `Core.AnyType.name`. -/
  anyTypeName : V
  /-- `_jl_type_hash(x)`. -/
  typeHash : X → M World (JInt .u64)
  /-- An `Int32` value. -/
  ofInt32 : JInt .i32 → V
  getfield : X → Sym → M World V

section
variable {L : Type}

/-- The `LineNumberNode` the parser records for a line of this file. -/
def lnn (line : Int) : Value L := .lineNumberNode (i64 line) (.symbol "deprecated.jl")

/-- `args[i]` (1-based). -/
def argAt (args : List (Value L)) (i : Nat) : MacroResult L (Value L) :=
  match JuliaLean.base.expr.argAt args i with
  | .ok v => .ok v
  | .error e => .error (.expr e)

/-- A `Bool` used as a condition; another value throws `TypeError`. -/
def asBool (lo : LeafOps L) : Value L → MacroResult L Bool
  | .leaf x => match lo.asBool x with
    | some b => pure b
    | none => throw (.expr .typeError)
  | _ => throw (.expr .typeError)

/-- `Symbol(name)`. -/
def mkSymbol (name : String) : MacroResult L (Value L) :=
  if name.contains '\x00' then throw (.expr (.jl (.argumentError "Symbol name may not contain \\0")))
  else pure (.symbol name)

/-- `Core.Typeof(x).name.singletonname`. -/
def singletonname (x : Value L) : Value L :=
  .expr "." [.expr "." [.expr "call" [.expr "." [.symbol "Core", .quoteNode (.symbol "Typeof")], x],
    .quoteNode (.symbol "name")], .quoteNode (.symbol "singletonname")]

end

-- Reason: The license line and the instructions to developers and release managers are comments.
-- UNTRANSLATED
-- Source: base/deprecated.jl:1-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Internal changes mechanism.
-- # Instructions for Julia Core Developers:
-- # 1. When making a breaking change that is known to be depended upon by an
-- #    important and closely coupled package, decide on a unique `change_name`
-- #    for your PR and add it to the list below. In general, it is better to
-- #    err on the side of caution and assign a `change_name` even if it is not
-- #    clear that it is required. `change_name`s may also be assigned after the
-- #    fact in a separate PR. (Note that this may cause packages to misbehave
-- #    on versions in between the change and the assignment of the `change_name`,
-- #    but this is often still better than the alternative of misbehaving on unknown
-- #    versions).
-- 
-- # Instructions for Release Managers:
-- # 1. Upon tagging any release, clear the list of internal changes.
-- # 2. Upon tagging an -alpha version
-- #    a. On master, set __next_removal_version to v"1.(x+1)-alpha"
-- #    b. On the release branch, set __next_removal_version to v"1.x" (no -alpha)
-- # 3. Upon tagging a release candidate, clear the list of internal changes and
-- #    set __next_removal_version to `nothing`.
-- /Source

/--
Julia source: base/deprecated.jl:22-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const __next_removal_version = v"1.12-alpha"
const __internal_changes_list = (
    :invertedlinetables,
    :codeinforefactor,
    :miuninferredrm,
    :codeinfonargs, #54341
    :ocnopartial,
    :printcodeinfocalls,
    :syntacticccall, #59165
    :svectvar, #61645
    :syntacticcglobal, #61709
    # Add new change names above this line
)

```
-/
def __next_removal_version : VersionNumber :=
  ⟨JInt.wrap .u32 1, JInt.wrap .u32 12, JInt.wrap .u32 0, [.text "alpha"], []⟩
def __internal_changes_list : List Sym :=
  ["invertedlinetables", "codeinforefactor", "miuninferredrm", "codeinfonargs", "ocnopartial",
   "printcodeinfocalls", "syntacticccall", "svectvar", "syntacticcglobal"]
-- Reason: This top-level check runs once when Base is built; it defines no method.
-- UNTRANSLATED
-- Source: base/deprecated.jl:36-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- if !isempty(__internal_changes_list)
--     if VERSION == __next_removal_version
--         error("You have tagged a new release without clearing the internal changes list.")
--     end
-- elseif __next_removal_version === nothing
--     error("You have tagged a new release candidate without clearing the internal changes list.")
-- end
-- 
-- /Source

/--
Julia source: base/deprecated.jl:44-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    __has_internal_change(version_or::VersionNumber, change_name::Symbol)

Some Julia packages have known dependencies on Julia internals (e.g. for introspection of
internal julia datastructures). To ease the co-development of such packages with julia,
a `change_name` is assigned on a best-effort basis or when explicitly requested.
This `change_name` can be used to probe whether or not the particular pre-release build of julia has
a particular change. In particular this function tests change scheduled for `version_or`
is present in our current julia build, either because our current version
is greater than `version_or` or because we're running a pre-release build that
includes the change.

Using this mechanism is a superior alternative to commit-number based `VERSION`
comparisons, which can be brittle during pre-release stages when there are multiple
actively developed branches.

The list of changes is cleared twice during the release process:
1. With the release of the first alpha
2. For the first release candidate

No new `change_name`s will be added during release candidates or bugfix releases
(so in particular on any released version, the list of changes will be empty and
`__has_internal_change` will always be equivalent to a version comparison.

# Example

Julia version `v"1.12.0-DEV.173"` changed the internal representation of line number debug info.
Several debugging packages have custom code to display this information and need to be changed
accordingly. In previous practice, this would often be accomplished with something like the following
```
@static if VERSION > v"1.12.0-DEV.173"
    # Code to handle new format
else
    # Code to handle old format
end
```

However, because such checks cannot be introduced until a VERSION number is assigned
(which also automatically pushes out the change to all nightly users), there was a builtin period
of breakage. With `__has_internal_change`, this can instead be written as:

```
@static if __has_internal_change(v"1.12-alpha", :invertedlinenames)
    # Code to handle new format
else
    # Code to handle old format
end
```

To find out the correct version to use as the first argument, you may use
`Base.__next_removal_version`, which is set to the next version number in which
the list of changes will be cleared.

The primary advantage of this approach is that it allows a new version of the
package to be tagged and released *in advance* of the break on the nightly
build, thus ensuring continuity of package operation for nightly users.

!!! warning

    This functionality is intended to help package developers which make use of
    internal julia functionality. Doing so is explicitly discouraged unless absolutely
    required and comes with the explicit understanding that the package will break.
    In particular, this is not a generic feature-testing mechanism, but only a
    simple, courtesy coordination mechanism for changes that are known (or found) to
    be breaking a package depending on julia internals.
"""
function __has_internal_change(version_or::VersionNumber, change_name::Symbol)
    VERSION > version_or && return true
    change_name in __internal_changes_list
end
````
-/
def __has_internal_change {Re : Type} (vops : VersionRegexOps Re) (VERSION : VersionNumber)
    (version_or : VersionNumber) (change_name : Sym) : Bool :=
  if versionLess vops version_or VERSION then true
  else __internal_changes_list.contains change_name
-- Reason: The export statement is load-time structure; the rest are comments.
-- UNTRANSLATED
-- Source: base/deprecated.jl:114-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- export __has_internal_change
-- 
-- # Deprecated functions and objects
-- #
-- # Please add new deprecations at the bottom of the file.
-- # A function deprecated in a release will be removed in the next one.
-- # Please also add a reference to the pull request which introduced the
-- # deprecation. For simple cases where a direct replacement is available,
-- # use @deprecate. @deprecate takes care of calling the replacement
-- # and of exporting the function.
-- #
-- # For more complex cases, move the body of the deprecated method in this file,
-- # and call depwarn() directly from inside it.
-- 
-- /Source
section
variable {L : Type} (mo : MacroOps L)

/--
Julia source: base/deprecated.jl:128-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @deprecate old new [export_old=true]

Deprecate method `old` and specify the replacement call `new`, defining a new method `old`
with the specified signature in the process.

To prevent `old` from being exported, set `export_old` to `false`.

See also [`Base.depwarn()`](@ref).

!!! compat "Julia 1.5"
    As of Julia 1.5, functions defined by `@deprecate` do not print warning when `julia`
    is run without the `--depwarn=yes` flag set, as the default value of `--depwarn` option
    is `no`.  The warnings are printed from tests run by `Pkg.test()`.

# Examples
```jldoctest
julia> @deprecate old_export(x) new(x)
old_export (generic function with 1 method)

julia> @deprecate old_public(x) new(x) false
old_public (generic function with 1 method)
```

Calls to `@deprecate` without explicit type-annotations will define
deprecated methods accepting any number of positional and keyword
arguments of type `Any`.

!!! compat "Julia 1.9"
    Keyword arguments are forwarded when there is no explicit type
    annotation as of Julia 1.9. For older versions, you can manually
    forward positional and keyword arguments by doing `@deprecate
    old(args...; kwargs...) new(args...; kwargs...)`.

To restrict deprecation to a specific signature, annotate the
arguments of `old`. For example,
```jldoctest; filter = r"@ .*"a
julia> new(x::Int) = x;

julia> new(x::Float64) = 2x;

julia> @deprecate old(x::Int) new(x);

julia> methods(old)
# 1 method for generic function "old" from Main:
 [1] old(x::Int64)
     @ deprecated.jl:94
```
will define and deprecate a method `old(x::Int)` that mirrors `new(x::Int)` but will not
define nor deprecate the method `old(x::Float64)`.
"""
macro deprecate(old, new, export_old=true)
    function cannot_export_nonsymbol()
        error(
            "if the third `export_old` argument is not specified or `true`, the first",
            " argument must be of form",
            " (1) `f(...)` where `f` is a symbol,",
            " (2) `T{...}(...)` where `T` is a symbol, or",
            " (3) a symbol.",
        )
    end
    meta = Expr(:meta, :noinline)
    if isa(old, Expr) && (old.head === :call || old.head === :where)
        remove_linenums!(new)
        oldcall = sprint(show_unquoted, old)
        newcall = sprint(show_unquoted, new)
        # if old.head is a :where, step down one level to the :call to avoid code duplication below
        callexpr = old.head === :call ? old : old.args[1]
        maybe_export = nothing
        if callexpr.head === :call
            fnexpr = callexpr.args[1]
            if fnexpr isa Expr && fnexpr.head === :curly
                fnexpr = fnexpr.args[1]
            end
            if export_old
                if fnexpr isa Symbol
                    maybe_export = Expr(:export, esc(fnexpr))
                else
                    cannot_export_nonsymbol()
                end
            end
        else
            error("invalid usage of @deprecate")
        end
        ex = :($(esc(old)) = begin
            $meta
            depwarn($"`$oldcall` is deprecated, use `$newcall` instead.", Core.Typeof($(esc(fnexpr))).name.singletonname)
            $(esc(new))
        end)
        Expr(:toplevel, maybe_export, replace_linenums!(ex, __source__))
    else
        if export_old && !(old isa Symbol)
            cannot_export_nonsymbol()
        end
        ex = :(function $(esc(old))(args...; kwargs...)
            $meta
            depwarn($"`$old` is deprecated, use `$new` instead.", Core.Typeof($(esc(old))).name.singletonname)
            $(esc(new))(args...; kwargs...)
        end)
        Expr(:toplevel,
            export_old ? Expr(:export, esc(old)) : nothing,
            replace_linenums!(ex, __source__))
    end
end

````
-/
def cannot_export_nonsymbol : MacroError L :=
  .expr (.errorException ("if the third `export_old` argument is not specified or `true`, the first" ++
    " argument must be of form" ++ " (1) `f(...)` where `f` is a symbol," ++
    " (2) `T{...}(...)` where `T` is a symbol, or" ++ " (3) a symbol."))

/-- `Expr(:meta, :noinline)`. -/
def deprecateMeta : Value L := .expr "meta" [.symbol "noinline"]

/-- The branch of `@deprecate` for an `old` that is not a `:call` or `:where` expression. -/
def deprecate_plain (source : JInt64 × Value L) (old new export_old : Value L) :
    MacroResult L (Option (Value L)) := do
  if (← asBool mo.lo export_old) && !(old matches .symbol _) then throw cannot_export_nonsymbol
  let msg := "`" ++ mo.string old ++ "` is deprecated, use `" ++ mo.string new ++ "` instead."
  let params : Value L := .expr "parameters" [.expr "..." [.symbol "kwargs"]]
  let args : Value L := .expr "..." [.symbol "args"]
  let ex : Value L := .expr "function" [.expr "call" [esc old, params, args],
    .expr "block" [lnn 222, lnn 223, deprecateMeta, lnn 224,
      .expr "call" [.symbol "depwarn", .leaf (mo.ofString msg), singletonname (esc old)],
      lnn 225, .expr "call" [esc new, params, args]]]
  let exported : Value L := if (← asBool mo.lo export_old) then .expr "export" [esc old]
    else .leaf mo.lo.nothing
  return (JuliaLean.base.expr.replace_linenums! mo.lo source ex).map fun ex =>
    .expr "toplevel" [exported, ex]

/-- `@deprecate old new [export_old=true]`, with `__source__` given as `(line, file)`. `none` is
an expansion that does not terminate (possible only when the file of `__source__` itself
contains line-number expressions). -/
def macro_deprecate (source : JInt64 × Value L) (old new : Value L)
    (export_old : Value L := .leaf (mo.lo.ofBool true)) : MacroResult L (Option (Value L)) := do
  match old with
  | .expr head oargs =>
    if head == "call" || head == "where" then
      let new := JuliaLean.base.expr.remove_linenums! mo.codeInfoNoLines new
      let oldcall := mo.showUnquoted old
      let newcall := mo.showUnquoted new
      -- if old.head is a :where, step down one level to the :call to avoid code duplication below
      let callexpr ← if head == "call" then pure old else argAt oargs 1
      let (maybe_export, fnexpr) ← match callexpr with
        | .expr "call" cargs => do
          let fnexpr ← argAt cargs 1
          let fnexpr ← match fnexpr with
            | .expr "curly" fargs => argAt fargs 1
            | f => pure f
          if (← asBool mo.lo export_old) then
            match fnexpr with
            | .symbol _ => pure (.expr "export" [esc fnexpr], fnexpr)
            | _ => throw cannot_export_nonsymbol
          else pure (.leaf mo.lo.nothing, fnexpr)
        | .expr _ _ => throw (.expr (.errorException "invalid usage of @deprecate"))
        | v => throw (.fieldError v "head")
      let msg := "`" ++ oldcall ++ "` is deprecated, use `" ++ newcall ++ "` instead."
      let ex : Value L := .expr "=" [esc old,
        .expr "block" [lnn 213, deprecateMeta, lnn 214,
          .expr "call" [.symbol "depwarn", .leaf (mo.ofString msg), singletonname (esc fnexpr)],
          lnn 215, esc new]]
      return (JuliaLean.base.expr.replace_linenums! mo.lo source ex).map fun ex =>
        .expr "toplevel" [maybe_export, ex]
    else deprecate_plain mo source old new export_old
  | _ => deprecate_plain mo source old new export_old

end
section
variable {World Ip Frame Mod : Type} (ops : DepOps World Ip Frame Mod)

/--
Julia source: base/deprecated.jl:291-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstcaller(bt::Vector, ::Nothing) = Ptr{Cvoid}(0), StackTraces.UNKNOWN
firstcaller(bt::Vector, funcsym::Symbol) = firstcaller(bt, (funcsym,))
function firstcaller(bt::Vector, funcsyms)
    # Identify the calling line
    found = false
    for ip in bt
        lkups = StackTraces.lookup(ip)
        for lkup in lkups
            if lkup == StackTraces.UNKNOWN || lkup.from_c
                continue
            end
            if found
                return ip, lkup
            end
            found = lkup.func in funcsyms
            # look for constructor type name
            if !found
                li = lkup.linfo
                if li isa Core.MethodInstance
                    def = li.def
                    found = def isa Method && def.name in funcsyms
                end
            end
        end
    end
    return C_NULL, StackTraces.UNKNOWN
end

```
-/
-- `firstcaller(bt::Vector, ::Nothing)`.
def firstcaller_nothing (_bt : List Ip) : Ip × Frame := (ops.cNull, ops.unknown)

/-- The inner loop of `firstcaller` over the frames of one instruction pointer: the final value of
`found`, or the returned `(ip, lkup)`. -/
def firstcaller_frames (funcsyms : List Sym) (ip : Ip) :
    Bool → List Frame → M World (Bool ⊕ (Ip × Frame))
  | found, [] => pure (.inl found)
  | found, lkup :: rest => do
    if (← ops.frameEq lkup ops.unknown) || ops.fromC lkup then
      firstcaller_frames funcsyms ip found rest
    else if found then pure (.inr (ip, lkup))
    else
      let found := funcsyms.contains (ops.func lkup)
      -- look for constructor type name
      let found := if !found then
          match ops.linfo lkup with
          | .method name _ => funcsyms.contains name
          | _ => false
        else found
      firstcaller_frames funcsyms ip found rest

/-- The outer loop of `firstcaller` over the backtrace. -/
def firstcaller_ips (funcsyms : List Sym) : Bool → List Ip → M World (Ip × Frame)
  | _, [] => pure (ops.cNull, ops.unknown)
  | found, ip :: rest => do
    let lkups ← ops.lookup ip
    match ← firstcaller_frames ops funcsyms ip found lkups with
    | .inr result => pure result
    | .inl found => firstcaller_ips funcsyms found rest

/-- `firstcaller(bt, funcsym)`, dispatching on `funcsym`. -/
def firstcaller (bt : List Ip) : FuncSym → M World (Ip × Frame)
  | .nothing => pure (firstcaller_nothing ops bt)
  | .sym s => firstcaller_ips ops [s] false bt
  | .syms funcsyms => firstcaller_ips ops funcsyms false bt
/--
Julia source: base/deprecated.jl:260-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function _depwarn(msg, funcsym, force::Bool)
    @nospecialize
    opts = JLOptions()
    if opts.depwarn == 2
        throw(ErrorException(msg))
    end
    deplevel = force || opts.depwarn == 1 ? CoreLogging.Warn : CoreLogging.BelowMinLevel
    @logmsg(
        deplevel,
        msg,
        _module=begin
            bt = backtrace()
            frame, caller = firstcaller(bt, funcsym)
            linfo = caller.linfo
            if linfo isa Core.MethodInstance
                def = linfo.def
                def isa Module ? def : def.module
            else
                Core    # TODO: Is it reasonable to attribute callers without linfo to Core?
            end
        end,
        _file=String(caller.file),
        _line=caller.line,
        _id=(frame,funcsym),
        _group=:depwarn,
        caller=caller,
        maxlog=funcsym === nothing ? nothing : 1
    )
    nothing
end

```
-/
def _depwarn (msg : String) (funcsym : FuncSym) (force : Bool) : M World Unit := do
  let depwarnOpt ← ops.optDepwarn
  if depwarnOpt.val == 2 then throw (.errorException msg)
  let deplevel := if force || depwarnOpt.val == 1 then LogLevel.warn else .belowMinLevel
  ops.logmsg deplevel msg (do
    let bt ← ops.backtrace
    let (frame, caller) ← firstcaller ops bt funcsym
    let _module := match ops.linfo caller with
      | .method _ m => m
      | .module m => m
      | .other => ops.core
    pure { _module, _file := ops.file caller, _line := ops.line caller, _id := (frame, funcsym),
           _group := "depwarn", caller,
           maxlog := match funcsym with
             | .nothing => none
             | _ => some (i64 1) })
/--
Julia source: base/deprecated.jl:233-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Base.depwarn(msg::String, funcsym::Symbol; force=false)

Print `msg` as a deprecation warning. The symbol `funcsym` should be the name
of the calling function, which is used to ensure that the deprecation warning is
only printed the first time for each call place. Set `force=true` to force the
warning to always be shown, even if Julia was started with `--depwarn=no` (the
default).

See also [`@deprecate`](@ref).

# Examples
```julia
function deprecated_func()
    Base.depwarn("Don't use `deprecated_func()`!", :deprecated_func)

    1 + 1
end
```
"""
@nospecializeinfer function depwarn(msg, funcsym; force::Bool=false)
    @nospecialize
    # N.B. With this use of `@invokelatest`, we're preventing the addition of backedges from
    # callees, such as `convert`, to this user-facing method. This approach is designed to
    # enhance the resilience of packages that utilize `depwarn` against invalidation.
    return @invokelatest _depwarn(msg, funcsym, force)
end
````
-/
def depwarn (msg : String) (funcsym : FuncSym) (force : Bool := false) : M World Unit :=
  _depwarn ops msg funcsym force
/--
Julia source: base/deprecated.jl:319-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deprecate(m::Module, s::Symbol, flag=1) = ccall(:jl_deprecate_binding, Cvoid, (Any, Any, Cint), m, s, flag)

```
-/
def deprecate {Mo : Type} (jl_deprecate_binding : Mo → Sym → JInt .i32 → M World Unit) (m : Mo)
    (s : Sym) (flag : JInt .i32 := JInt.wrap .i32 1) : M World Unit :=
  jl_deprecate_binding m s flag

end
section
variable {L : Type} (mo : MacroOps L)

/--
Julia source: base/deprecated.jl:321-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @deprecate_binding old new [export_old=true] [dep_message] [constant=true]

Deprecate the binding `old`, making it an alias for `new` and printing a deprecation warning
on access to `old` (when `julia` is run with `--depwarn=yes`). This is for deprecating a
renamed or relocated global/constant, whereas [`@deprecate`](@ref) is for deprecating methods.

`old` must be a symbol and `new` the replacement it forwards to. By default `old` is defined
as a `const`; pass `false` for `constant` to define it as a non-constant global instead.

To prevent `old` from being exported, set `export_old` to `false`. A custom `dep_message`
string (printed after "<module>.old is deprecated") may be given.

See also [`@deprecate`](@ref) and [`Base.depwarn`](@ref).

# Examples
```jldoctest
julia> const dep_new = 42;

julia> Base.@deprecate_binding dep_old dep_new false;

julia> dep_old
42
```
"""
macro deprecate_binding(old, new, export_old=true, dep_message=:nothing, constant=true)
    dep_message === :nothing && (dep_message = ", use $new instead.")
    return Expr(:toplevel,
         export_old ? Expr(:export, esc(old)) : nothing,
         Expr(:const, Expr(:(=), esc(Symbol(string("_dep_message_",old))), esc(dep_message))),
         constant ? Expr(:const, Expr(:(=), esc(old), esc(new))) : Expr(:(=), esc(old), esc(new)),
         Expr(:call, :deprecate, __module__, Expr(:quote, old)))
end

````
-/
def macro_deprecate_binding (__module__ : L) (old new : Value L)
    (export_old : Value L := .leaf (mo.lo.ofBool true)) (dep_message : Value L := .symbol "nothing")
    (constant : Value L := .leaf (mo.lo.ofBool true)) : MacroResult L (Value L) := do
  let dep_message : Value L := if dep_message matches .symbol "nothing" then
      .leaf (mo.ofString (", use " ++ mo.string new ++ " instead."))
    else dep_message
  let exported : Value L := if (← asBool mo.lo export_old) then .expr "export" [esc old]
    else .leaf mo.lo.nothing
  let msgName ← mkSymbol ("_dep_message_" ++ mo.string old)
  let binding : Value L := if (← asBool mo.lo constant) then .expr "const" [.expr "=" [esc old, esc new]]
    else .expr "=" [esc old, esc new]
  return .expr "toplevel" [exported, .expr "const" [.expr "=" [esc msgName, esc dep_message]], binding,
    .expr "call" [.symbol "deprecate", .leaf __module__, .expr "quote" [old]]]
/--
Julia source: base/deprecated.jl:355-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro deprecate_stdlib(old, mod, export_old=true, newname=old)
    rename = old === newname ? "" : " as `$newname`"
    dep_message = """: it has been moved to the standard library package `$mod`$rename.
                        Add `using $mod` to your imports."""
    new = GlobalRef(Base.root_module(Base, mod), newname)
    return Expr(:toplevel,
         export_old ? Expr(:export, esc(old)) : nothing,
         Expr(:const, Expr(:(=), esc(Symbol(string("_dep_message_",old))), esc(dep_message))),
         Expr(:const, Expr(:(=), esc(old), esc(new))),
         Expr(:call, :deprecate, __module__, Expr(:quote, old)))
end

```
-/
def macro_deprecate_stdlib (__module__ : L) (old mod : Value L)
    (export_old : Value L := .leaf (mo.lo.ofBool true)) (newname : Value L := old) :
    MacroResult L (Value L) := do
  let rename := if JuliaLean.base.expr.egal mo.lo old newname then ""
    else " as `" ++ mo.string newname ++ "`"
  let dep_message := ": it has been moved to the standard library package `" ++ mo.string mod ++ "`" ++
    rename ++ ".\nAdd `using " ++ mo.string mod ++ "` to your imports."
  let root ← mo.rootModule mod
  let new : Value L ← match newname with
    | .symbol n => pure (.globalRef root n)
    | _ => throw (.expr (.jl (.methodError "GlobalRef")))
  let exported : Value L := if (← asBool mo.lo export_old) then .expr "export" [esc old]
    else .leaf mo.lo.nothing
  let msgName ← mkSymbol ("_dep_message_" ++ mo.string old)
  return .expr "toplevel" [exported,
    .expr "const" [.expr "=" [esc msgName, esc (.leaf (mo.ofString dep_message))]],
    .expr "const" [.expr "=" [esc old, esc new]],
    .expr "call" [.symbol "deprecate", .leaf __module__, .expr "quote" [old]]]
/--
Julia source: base/deprecated.jl:367-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro deprecate_moved(old, new, export_old=true)
    eold = esc(old)
    emsg = string(old, " has been moved to the package ", new, ".jl.\n",
        "Run `Pkg.add(\"", new, "\")` to install it, restart Julia,\n",
        "and then run `using ", new, "` to load it.")
    return Expr(:toplevel,
        replace_linenums!(:($eold(args...; kwargs...) = error($emsg)), __source__),
        export_old ? Expr(:export, eold) : nothing,
        Expr(:call, :deprecate, __module__, Expr(:quote, old), 2))
end

# BEGIN 1.0 deprecations

```
-/
-- `@deprecate_moved old new [export_old=true]`; `none` is an expansion that does not
-- terminate (see `macro_deprecate`).
def macro_deprecate_moved (source : JInt64 × Value L) (__module__ : L) (old new : Value L)
    (export_old : Value L := .leaf (mo.lo.ofBool true)) : MacroResult L (Option (Value L)) := do
  let eold := esc old
  let emsg := mo.string old ++ " has been moved to the package " ++ mo.string new ++ ".jl.\n" ++
    "Run `Pkg.add(\"" ++ mo.string new ++ "\")` to install it, restart Julia,\n" ++
    "and then run `using " ++ mo.string new ++ "` to load it."
  let method : Value L := .expr "=" [
    .expr "call" [eold, .expr "parameters" [.expr "..." [.symbol "kwargs"]], .expr "..." [.symbol "args"]],
    .expr "block" [lnn 373, .expr "call" [.symbol "error", .leaf (mo.ofString emsg)]]]
  match JuliaLean.base.expr.replace_linenums! mo.lo source method with
  | none => return none
  | some method =>
    let exported : Value L := if (← asBool mo.lo export_old) then .expr "export" [eold]
      else .leaf mo.lo.nothing
    return some (.expr "toplevel" [method, exported,
      .expr "call" [.symbol "deprecate", .leaf __module__, .expr "quote" [old], .leaf (mo.lo.ofInt (i64 2))]])

end
section
variable {World Ip Frame Mod : Type} (ops : DepOps World Ip Frame Mod)

/--
Julia source: base/deprecated.jl:380-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate one(i::CartesianIndex)                    oneunit(i)
```
-/
def one_CartesianIndex {I : Type} (oneunit : I → M World I) (i : I) : M World I := do
  depwarn ops "`one(i::CartesianIndex)` is deprecated, use `oneunit(i)` instead." (.sym "one")
  oneunit i
/--
Julia source: base/deprecated.jl:381-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate one(I::Type{CartesianIndex{N}}) where {N} oneunit(I)

```
-/
def one_Type_CartesianIndex {T : Type} (oneunit : T → M World T) (I : T) : M World T := do
  depwarn ops "`one(I::Type{CartesianIndex{N}}) where N` is deprecated, use `oneunit(I)` instead." (.sym "one")
  oneunit I
-- Reason: This import of `BigFloat` from `MPFR` is load-time structure.
-- UNTRANSLATED
-- Source: base/deprecated.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- import .MPFR: BigFloat
-- /Source

/--
Julia source: base/deprecated.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate BigFloat(x, prec::Int)                               BigFloat(x; precision=prec)
```
-/
def BigFloat_prec {X B : Type} (bigFloat : X → JInt64 → M World B) (x : X) (prec : JInt64) :
    M World B := do
  depwarn ops "`BigFloat(x, prec::Int)` is deprecated, use `BigFloat(x; precision = prec)` instead." (.sym "AnyType")
  bigFloat x prec
/--
Julia source: base/deprecated.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate BigFloat(x, prec::Int, rounding::RoundingMode)       BigFloat(x, rounding; precision=prec)
```
-/
def BigFloat_prec_rounding {X R B : Type} (bigFloat : X → R → JInt64 → M World B) (x : X)
    (prec : JInt64) (rounding : R) : M World B := do
  depwarn ops "`BigFloat(x, prec::Int, rounding::RoundingMode)` is deprecated, use `BigFloat(x, rounding; precision = prec)` instead." (.sym "AnyType")
  bigFloat x rounding prec
/--
Julia source: base/deprecated.jl:386-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate BigFloat(x::Real, prec::Int)                         BigFloat(x; precision=prec)
```
-/
def BigFloat_Real_prec {X B : Type} (bigFloat : X → JInt64 → M World B) (x : X) (prec : JInt64) :
    M World B := do
  depwarn ops "`BigFloat(x::Real, prec::Int)` is deprecated, use `BigFloat(x; precision = prec)` instead." (.sym "AnyType")
  bigFloat x prec
/--
Julia source: base/deprecated.jl:387-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate BigFloat(x::Real, prec::Int, rounding::RoundingMode) BigFloat(x, rounding; precision=prec)

# END 1.0 deprecations

# BEGIN 1.5 deprecations

```
-/
def BigFloat_Real_prec_rounding {X R B : Type} (bigFloat : X → R → JInt64 → M World B) (x : X)
    (prec : JInt64) (rounding : R) : M World B := do
  depwarn ops "`BigFloat(x::Real, prec::Int, rounding::RoundingMode)` is deprecated, use `BigFloat(x, rounding; precision = prec)` instead." (.sym "AnyType")
  bigFloat x rounding prec

end
/--
Julia source: base/deprecated.jl:393-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isimmutable(v) -> Bool
!!! warning
    Consider using `!ismutable(v)` instead, as `isimmutable(v)` will be replaced by `!ismutable(v)` in a future release. (Since Julia 1.5)
Return `true` iff value `v` is immutable.  See [Mutable Composite Types](@ref)
for a discussion of immutability. Note that this function works on values, so if you give it
a type, it will tell you that a value of `DataType` is mutable.

# Examples
```jldoctest
julia> isimmutable(1)
true

julia> isimmutable([1,2])
false
```
"""
isimmutable(@nospecialize(x)) = !ismutable(x)
````
-/
def isimmutable {X : Type} (ismutable : X → Bool) (x : X) : Bool := !ismutable x
-- Reason: The export statement is load-time structure; the rest is a comment.
-- UNTRANSLATED
-- Source: base/deprecated.jl:411-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- export isimmutable
-- # Note isimmutable is not @deprecated out of performance concerns
-- 
-- /Source
section
variable {L : Type} (mo : MacroOps L)

/--
Julia source: base/deprecated.jl:414-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro get!(h, key0, default)
    f, l = __source__.file, __source__.line
    @warn "`@get!(dict, key, default)` at $f:$l is deprecated, use `get!(()->default, dict, key)` instead."
    return quote
        get!(()->$(esc(default)), $(esc(h)), $(esc(key0)))
    end
end

```
-/
-- `@get!(h, key0, default)`; `warn` is the `@warn` logging call.
def macro_get! {World : Type} (warn : String → M World Unit) (source : JInt64 × Value L)
    (h key0 default : Value L) : M World (Value L) := do
  let (l, f) := source
  warn ("`@get!(dict, key, default)` at " ++ mo.string f ++ ":" ++ toString l.val ++
    " is deprecated, use `get!(()->default, dict, key)` instead.")
  return .expr "block" [lnn 418,
    .expr "call" [.symbol "get!", .expr "->" [.expr "tuple" [], .expr "block" [lnn 418, esc default]],
      esc h, esc key0]]

end
/--
Julia source: base/deprecated.jl:422-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(V::SubArray{<:Any,<:Any,<:Array,<:Tuple{Vararg{RangeIndex}}}, is::Tuple) = pointer(V, CartesianIndex(is))

# END 1.5 deprecations

# BEGIN 1.6 deprecations

# These changed from SimpleVector to `MethodMatch`. These definitions emulate
# being a SimpleVector to ease transition for packages that make explicit
# use of (internal) APIs that return raw method matches.
```
-/
def pointer_SubArray {World V T C P : Type} (pointer : V → C → M World P)
    (CartesianIndex : T → M World C) (V' : V) (is : T) : M World P := do
  pointer V' (← CartesianIndex is)
/--
Julia source: base/deprecated.jl:431-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(match::Core.MethodMatch, field::Int=1) =
    field > nfields(match) ? nothing : (getfield(match, field), field+1)
```
-/
def iterate_MethodMatch {World MM F : Type} (nfields : MM → JInt64) (getfield : MM → JInt64 → M World F)
    (match' : MM) (field : JInt64 := i64 1) : M World (Option (F × JInt64)) := do
  if field.val > (nfields match').val then return none
  return some (← getfield match' field, field + i64 1)
/--
Julia source: base/deprecated.jl:433-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(match::Core.MethodMatch, field::Int) =
    getfield(match, field)


# these were internal functions, but some packages seem to be relying on them
```
-/
def getindex_MethodMatch {World MM F : Type} (getfield : MM → JInt64 → M World F) (match' : MM)
    (field : JInt64) : M World F :=
  getfield match' field
/--
Julia source: base/deprecated.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tuple_type_head(T::Type) = fieldtype(T, 1)
```
-/
def tuple_type_head {World Ty : Type} (fieldtype : Ty → JInt64 → M World Ty) (T : Ty) : M World Ty :=
  fieldtype T (i64 1)
/--
Julia source: base/deprecated.jl:439-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tuple_type_cons(::Type, ::Type{Union{}}) = Union{}
```
-/
-- `tuple_type_cons(S, T)`, dispatching on `T`: `Union{}`, a subtype of `Tuple`, or another type
-- (no method).
def tuple_type_cons {World Ty : Type} (ops : TupleTypeOps World Ty) (S T : Ty) : M World Ty := do
  if ops.isBottom T then return ops.bottom
  if !ops.isTupleType T then throw (.jl (.methodError "tuple_type_cons"))
  ops.tupleOf (S :: (← ops.parameters T))
/--
Julia source: base/deprecated.jl:440-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable tuple_type_cons(::Type{S}, ::Type{T}) where T<:Tuple where S =
    Tuple{S, T.parameters...}
```
-/
-- The `T <: Tuple` method of `tuple_type_cons`.
def tuple_type_cons_Tuple {World Ty : Type} (ops : TupleTypeOps World Ty) (S T : Ty) : M World Ty := do
  ops.tupleOf (S :: (← ops.parameters T))
/--
Julia source: base/deprecated.jl:442-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable parameter_upper_bound(t::UnionAll, idx) =
    rewrap_unionall((unwrap_unionall(t)::DataType).parameters[idx], t)

# these were internal functions, but some packages seem to be relying on them
```
-/
def parameter_upper_bound {World Ty DT P I : Type} (unwrap_unionall : Ty → Ty)
    (asDataType : Ty → Option DT) (parameters : DT → I → M World P) (rewrap_unionall : P → Ty → M World Ty)
    (t : Ty) (idx : I) : M World Ty := do
  match asDataType (unwrap_unionall t) with
  | some dt => rewrap_unionall (← parameters dt idx) t
  | none => throw (.foreignError "TypeError" "in typeassert, expected DataType")
/--
Julia source: base/deprecated.jl:446-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate cat_shape(dims, shape::Tuple{}, shapes::Tuple...) cat_shape(dims, shapes) false
```
-/
def cat_shape_shapes {World D S R : Type} (cat_shape : D → List S → M World R)
    {Ip Frame Mod : Type} (ops : DepOps World Ip Frame Mod) (dims : D) (shapes : List S) : M World R := do
  depwarn ops "`cat_shape(dims, shape::Tuple{}, shapes::Tuple...)` is deprecated, use `cat_shape(dims, shapes)` instead." (.sym "cat_shape")
  cat_shape dims shapes
/--
Julia source: base/deprecated.jl:447-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_shape(dims, shape::Tuple{}) = () # make sure `cat_shape(dims, ())` do not recursively calls itself

```
-/
def cat_shape_empty {D : Type} (_dims : D) : Unit := ()
section
variable {World Ip Frame Mod : Type} (ops : DepOps World Ip Frame Mod)

/--
Julia source: base/deprecated.jl:449-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate unsafe_indices(A) axes(A) false
```
-/
def unsafe_indices {A R : Type} (axes : A → M World R) (A' : A) : M World R := do
  depwarn ops "`unsafe_indices(A)` is deprecated, use `axes(A)` instead." (.sym "unsafe_indices")
  axes A'
/--
Julia source: base/deprecated.jl:450-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate unsafe_length(r) length(r) false

# these were internal type aliases, but some packages seem to be relying on them
```
-/
def unsafe_length {R N : Type} (length : R → M World N) (r : R) : M World N := do
  depwarn ops "`unsafe_length(r)` is deprecated, use `length(r)` instead." (.sym "unsafe_length")
  length r
-- Reason: `Any16` and `All16` are type aliases (load-time definitions with no method); the rest are comments.
-- UNTRANSLATED
-- Source: base/deprecated.jl:453-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const Any16{N} = Tuple{Any,Any,Any,Any,Any,Any,Any,Any,
--                         Any,Any,Any,Any,Any,Any,Any,Any,Vararg{Any,N}}
-- const All16{T,N} = Tuple{T,T,T,T,T,T,T,T,
--                          T,T,T,T,T,T,T,T,Vararg{T,N}}
-- 
-- # END 1.6 deprecations
-- 
-- # BEGIN 1.7 deprecations
-- 
-- # the plan is to eventually overload getproperty to access entries of the dict
-- /Source

/--
Julia source: base/deprecated.jl:463-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function getproperty(x::Pairs, s::Symbol)
    s == :data && depwarn("use values(kwargs) instead of kwargs.data", :getproperty, force=true)
    s == :itr && depwarn("use keys(kwargs) instead of kwargs.itr", :getproperty, force=true)
    return getfield(x, s)
end

# This function was marked as experimental and not exported.
```
-/
def getproperty_Pairs {X V : Type} (getfield : X → Sym → M World V) (x : X) (s : Sym) : M World V := do
  if s == "data" then depwarn ops "use values(kwargs) instead of kwargs.data" (.sym "getproperty") (force := true)
  if s == "itr" then depwarn ops "use keys(kwargs) instead of kwargs.itr" (.sym "getproperty") (force := true)
  getfield x s
/--
Julia source: base/deprecated.jl:470-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate catch_stack(task=current_task(); include_bt=true) current_exceptions(task; backtrace=include_bt) false

# END 1.7 deprecations

# BEGIN 1.8 deprecations

```
-/
def catch_stack {T R : Type} (current_task : M World T) (current_exceptions : T → Bool → M World R)
    (task : Option T := none) (include_bt : Bool := true) : M World R := do
  let task ← match task with
    | some t => pure t
    | none => current_task
  depwarn ops "`catch_stack(task = current_task(); include_bt = true)` is deprecated, use `current_exceptions(task; backtrace = include_bt)` instead." (.sym "catch_stack")
  current_exceptions task include_bt
-- Reason: These bind the names `@_inline_meta` and `@_noinline_meta` to the macros `@inline` and `@noinline` (load-time aliases with no method).
-- UNTRANSLATED
-- Source: base/deprecated.jl:476-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const var"@_inline_meta" = var"@inline"
-- const var"@_noinline_meta" = var"@noinline"
-- /Source

/--
Julia source: base/deprecated.jl:478-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate getindex(t::Tuple, i::Real) t[convert(Int, i)]

# END 1.8 deprecations

# BEGIN 1.9 deprecations

# We'd generally like to avoid direct external access to internal fields
# Core.Compiler.is_inlineable and Core.Compiler.set_inlineable! move towards this direction,
# but we need to keep these around for compat
```
-/
def getindex_Tuple_Real {T R V : Type} (convertInt : R → M World JInt64) (getindex : T → JInt64 → M World V)
    (t : T) (i : R) : M World V := do
  depwarn ops "`getindex(t::Tuple, i::Real)` is deprecated, use `t[convert(Int, i)]` instead." (.sym "getindex")
  getindex t (← convertInt i)

end
/--
Julia source: base/deprecated.jl:487-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getproperty(ci::CodeInfo, s::Symbol)
    s === :inlineable && return Core.Compiler.is_inlineable(ci)
    return getfield(ci, s)
end

```
-/
def getproperty_CodeInfo {World CI V : Type} (is_inlineable : CI → M World V) (getfield : CI → Sym → M World V)
    (ci : CI) (s : Sym) : M World V := do
  if s == "inlineable" then return (← is_inlineable ci)
  getfield ci s
/--
Julia source: base/deprecated.jl:492-496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setproperty!(ci::CodeInfo, s::Symbol, v)
    s === :inlineable && return Core.Compiler.set_inlineable!(ci, v)
    return setfield!(ci, s, convert(fieldtype(CodeInfo, s), v))
end

```
-/
def setproperty_CodeInfo {World CI V Ty R : Type} (set_inlineable! : CI → V → M World R)
    (fieldtype : Sym → M World Ty) (convert : Ty → V → M World V) (setfield! : CI → Sym → V → M World R)
    (ci : CI) (s : Sym) (v : V) : M World R := do
  if s == "inlineable" then return (← set_inlineable! ci v)
  setfield! ci s (← convert (← fieldtype s) v)
/--
Julia source: base/deprecated.jl:497-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval Threads nthreads() = threadpoolsize()

```
-/
-- `Threads.nthreads()`.
def nthreads {World : Type} (threadpoolsize : M World JInt64) : M World JInt64 := threadpoolsize
/--
Julia source: base/deprecated.jl:499-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval Threads begin
    """
        resize_nthreads!(A, copyvalue=A[1])

    Resize the array `A` to length [`nthreads()`](@ref).   Any new
    elements that are allocated are initialized to `deepcopy(copyvalue)`,
    where `copyvalue` defaults to `A[1]`.

    This is typically used to allocate per-thread variables, and
    should be called in `__init__` if `A` is a global constant.

    !!! warning

        This function is deprecated, since as of Julia v1.9 the number of
        threads can change at run time. Instead, per-thread state should be
        created as needed based on the thread id of the caller.
    """
    function resize_nthreads!(A::AbstractVector, copyvalue=A[1])
        nthr = nthreads()
        nold = length(A)
        resize!(A, nthr)
        for i = nold+1:nthr
            A[i] = deepcopy(copyvalue)
        end
        return A
    end
end

# END 1.9 deprecations

# BEGIN 1.10 deprecations

```
-/
-- The vector operations of `Threads.resize_nthreads!`.
structure VectorOps (World A V : Type) where
  getindex : A → JInt64 → M World V
  length : A → M World JInt64
  resize! : A → JInt64 → M World Unit
  setindex! : A → JInt64 → V → M World Unit
  deepcopy : V → M World V

/-- The elements of `a:b`. -/
def intRange (a b : JInt64) : List JInt64 :=
  (List.range (b.val - a.val + 1).toNat).map fun (k : Nat) => i64 (a.val + k)

def resize_nthreads! {World A V : Type} (ops : VectorOps World A V) (threadpoolsize : M World JInt64)
    (A' : A) (copyvalue : Option V := none) : M World A := do
  let copyvalue ← match copyvalue with
    | some v => pure v
    | none => ops.getindex A' (i64 1)
  let nthr ← nthreads threadpoolsize
  let nold ← ops.length A'
  ops.resize! A' nthr
  for i in intRange (nold + i64 1) nthr do
    ops.setindex! A' i (← ops.deepcopy copyvalue)
  return A'
section
variable {L : Type}

/--
Julia source: base/deprecated.jl:531-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @pure ex

`@pure` gives the compiler a hint for the definition of a pure function,
helping for type inference.

!!! warning
    This macro is intended for internal compiler use and may be subject to changes.

!!! warning
    In Julia 1.8 and higher, it is favorable to use [`@assume_effects`](@ref) instead of `@pure`.
    This is because `@assume_effects` allows a finer grained control over Julia's purity
    modeling and the effect system enables a wider range of optimizations.
"""
macro pure(ex)
    return esc(:(Base.@assume_effects :foldable $ex))
end

# END 1.10 deprecations

# BEGIN 1.11 deprecations

# these were never a part of the public API and so they can be removed without deprecation
# in a minor release but we're being nice and trying to avoid transient breakage.
```
-/
def macro_pure (ex : Value L) : Value L :=
  esc (.expr "macrocall" [.expr "." [.symbol "Base", .quoteNode (.symbol "@assume_effects")], lnn 546,
    .quoteNode (.symbol "foldable"), ex])

end
section
variable {World Ip Frame Mod : Type} (ops : DepOps World Ip Frame Mod)

/--
Julia source: base/deprecated.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate permute!!(a, p::AbstractVector{<:Integer}) permute!(a, p) false
```
-/
def permute!!_shim {A P R : Type} (permute! : A → P → M World R) (a : A) (p : P) : M World R := do
  depwarn ops "`permute!!(a, p::AbstractVector{<:Integer})` is deprecated, use `permute!(a, p)` instead." (.sym "permute!!")
  permute! a p
/--
Julia source: base/deprecated.jl:556-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate invpermute!!(a, p::AbstractVector{<:Integer}) invpermute!(a, p) false

# END 1.11 deprecations

# BEGIN 1.12 deprecations

```
-/
def invpermute!!_shim {A P R : Type} (invpermute! : A → P → M World R) (a : A) (p : P) : M World R := do
  depwarn ops "`invpermute!!(a, p::AbstractVector{<:Integer})` is deprecated, use `invpermute!(a, p)` instead." (.sym "invpermute!!")
  invpermute! a p
/--
Julia source: base/deprecated.jl:562-563 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate isbindingresolved(m::Module, var::Symbol) true false

```
-/
def isbindingresolved {Mo : Type} (_m : Mo) (_var : Sym) : M World Bool := do
  depwarn ops "`isbindingresolved(m::Module, var::Symbol)` is deprecated, use `true` instead." (.sym "isbindingresolved")
  return true
-- Reason: This docstring attaches to the existing binding `isbindingresolved` and defines no method; the rest is a comment.
-- UNTRANSLATED
-- Source: base/deprecated.jl:564-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isbindingresolved(m::Module, s::Symbol) -> Bool
-- 
-- Return whether the binding of a symbol in a module is resolved.
-- 
-- See also [`isexported`](@ref), [`ispublic`](@ref), [`isdeprecated`](@ref).
-- 
-- ```jldoctest
-- julia> module Mod
--            foo() = 17
--        end
-- Mod
-- 
-- julia> Base.isbindingresolved(Mod, :foo)
-- true
-- ```
-- 
-- !!! warning
--     This function is deprecated. The concept of binding "resolvedness" was removed in Julia 1.12.
--     The function now always returns `true`.
-- """
-- isbindingresolved
-- 
-- # Some packages call this function
-- /Source

/--
Julia source: base/deprecated.jl:588-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function to_power_type(x::Number)
    T = promote_type(typeof(x), typeof(x*x))
    convert(T, x)
end
```
-/
def to_power_type_Number {X T : Type} (mul : X → X → M World X) (typeof : X → T)
    (promote_type : T → T → M World T) (convert : T → X → M World X) (x : X) : M World X := do
  let T' ← promote_type (typeof x) (typeof (← mul x x))
  convert T' x
/--
Julia source: base/deprecated.jl:592-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_power_type(x) = oftype(x*x, x)

# END 1.12 deprecations

# BEGIN 1.13 deprecations

@deprecate merge(combine::Callable, d::AbstractDict, others::AbstractDict...) mergewith(combine, d, others...)

# end 1.13 deprecations

# BEGIN 1.14 deprecations

# These operators are new in 1.14, but these fallback methods are added for
# compatibility while packages adjust to defining both operators, to allow
# Base and other packages to start using these.
```
-/
def to_power_type {X : Type} (mul : X → X → M World X) (oftype : X → X → M World X) (x : X) : M World X := do
  oftype (← mul x x) x
/--
Julia source: base/deprecated.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*%(a::T, b::T) where {T} = *(a, b)
```
-/
-- The operations of the `*%`, `+%` and `-%` fallbacks.
structure WrapOpOps (World X : Type) where
  /-- `typeof(a) === typeof(b)`. -/
  sameType : X → X → Bool
  /-- `a isa IEEEFloat`. -/
  isIEEEFloat : X → Bool

/-- `*%(a, b)`: the method for two values of one type, and its `IEEEFloat` refusal. -/
def mulWrap {X : Type} (wops : WrapOpOps World X) (mul : X → X → M World X) (a b : X) : M World X := do
  if !wops.sameType a b then throw (.jl (.methodError "*%"))
  if wops.isIEEEFloat a then throw (.jl (.methodError "*%"))
  mul a b
/--
Julia source: base/deprecated.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+%(a::T, b::T) where {T} = +(a, b)
```
-/
def addWrap {X : Type} (wops : WrapOpOps World X) (add : X → X → M World X) (a b : X) : M World X := do
  if !wops.sameType a b then throw (.jl (.methodError "+%"))
  if wops.isIEEEFloat a then throw (.jl (.methodError "+%"))
  add a b
/--
Julia source: base/deprecated.jl:609-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(a::T, b::T) where {T} = -(a, b)

```
-/
def subWrap {X : Type} (wops : WrapOpOps World X) (sub : X → X → M World X) (a b : X) : M World X := do
  if !wops.sameType a b then throw (.jl (.methodError "-%"))
  if wops.isIEEEFloat a then throw (.jl (.methodError "-%"))
  sub a b
/--
Julia source: base/deprecated.jl:611-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*%(a::T, b::T) where {T<:IEEEFloat} = throw(MethodError(*%, (a, b)))
```
-/
-- `*%(a::T, b::T) where {T<:IEEEFloat}`.
def mulWrap_IEEEFloat {X : Type} (_a _b : X) : M World X := throw (.jl (.methodError "*%"))
/--
Julia source: base/deprecated.jl:612-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+%(a::T, b::T) where {T<:IEEEFloat} = throw(MethodError(+%, (a, b)))
```
-/
def addWrap_IEEEFloat {X : Type} (_a _b : X) : M World X := throw (.jl (.methodError "+%"))
/--
Julia source: base/deprecated.jl:613-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(a::T, b::T) where {T<:IEEEFloat} = throw(MethodError(-%, (a, b)))

# Revise calls this
```
-/
def subWrap_IEEEFloat {X : Type} (_a _b : X) : M World X := throw (.jl (.methodError "-%"))
/--
Julia source: base/deprecated.jl:616-629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function explicit_manifest_entry_path(args...)
    spec = explicit_manifest_entry_load_spec(args...)
    spec === nothing && return nothing
    return spec.path
end

# These functions get called from generated functions a lot where printing causes errors. We have the following options:
# 1. Use ordinary depwarn. This breaks generated functions that use these deprecations, defeating the point.
# 2. Always error in generated functions. This would probably be best (the depwarn would run at expansion time),
#    but it completely breaks inference of these generated functions and some of them are important.
# 3. Never print a warning in generated functions (but do throw the error if --depwarn=error).
#
# We choose option 3. It's not ideal, because users that never use --depwarn=error will never see the warning,
# but it's the least bad tradeoff among the lot.
```
-/
def explicit_manifest_entry_path {A S P : Type} (explicit_manifest_entry_load_spec : A → M World (Option S))
    (path : S → M World P) (args : A) : M World (Option P) := do
  match ← explicit_manifest_entry_load_spec args with
  | none => return none
  | some spec => return some (← path spec)
/--
Julia source: base/deprecated.jl:630-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function depwarn_if_not_pure(args...)
    opts = JLOptions()
    opts.depwarn != 2 && ccall(:jl_is_in_pure_context, Bool, ()) && return
    depwarn(args...)
end

```
-/
def depwarn_if_not_pure (msg : String) (funcsym : FuncSym) : M World Unit := do
  let opts ← ops.optDepwarn
  if opts.val != 2 && (← ops.isInPureContext) then return
  depwarn ops msg funcsym
/--
Julia source: base/deprecated.jl:636-649 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function getproperty(x::TypeEq, s::Symbol)
    if s === :parameters
        depwarn_if_not_pure("accessing `Type.parameters` is deprecated; use `Base.type_parameter(x)` instead", :getproperty)
        return Core.svec(type_parameter(x))
    elseif s === :name
        depwarn_if_not_pure("accessing `Type.name` is deprecated without replacement. If for detection, use `Base.isType(x)`.", :getproperty)
        return Core.AnyType.name
    elseif s === :hash
        depwarn_if_not_pure("accessing `Type.hash` is deprecated; use `Base._jl_type_hash(x)` instead", :getproperty)
        return reinterpret(Int32, UInt32(_jl_type_hash(x)))
    end
    return getfield(x, s)
end

```
-/
-- The `Int32` `reinterpret(Int32, UInt32(h))` of a type hash.
def hashInt32 (h : JInt .u64) : M World (JInt .i32) := do
  if h.val ≤ 4294967295 then return JInt.wrap .i32 h.val
  throw (.jl (.inexactError "UInt32"))

def getproperty_TypeEq {X V : Type} (tops : TypePropertyOps World X V) (x : X) (s : Sym) : M World V := do
  if s == "parameters" then
    depwarn_if_not_pure ops "accessing `Type.parameters` is deprecated; use `Base.type_parameter(x)` instead" (.sym "getproperty")
    return (← tops.svecTypeParameter x)
  else if s == "name" then
    depwarn_if_not_pure ops "accessing `Type.name` is deprecated without replacement. If for detection, use `Base.isType(x)`." (.sym "getproperty")
    return tops.anyTypeName
  else if s == "hash" then
    depwarn_if_not_pure ops "accessing `Type.hash` is deprecated; use `Base._jl_type_hash(x)` instead" (.sym "getproperty")
    return tops.ofInt32 (← hashInt32 (← tops.typeHash x))
  tops.getfield x s
/--
Julia source: base/deprecated.jl:650-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function typename(x::TypeEq)
    depwarn_if_not_pure("calling `typename` on `Type` is deprecated. If for detection, use `Base.isType(x)`.", :typename)
    return Core.AnyType.name
end

```
-/
def typename_TypeEq {X V : Type} (tops : TypePropertyOps World X V) (_x : X) : M World V := do
  depwarn_if_not_pure ops "calling `typename` on `Type` is deprecated. If for detection, use `Base.isType(x)`." (.sym "typename")
  return tops.anyTypeName
/--
Julia source: base/deprecated.jl:655-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function nameof(x::TypeEq)
    depwarn_if_not_pure("calling `nameof` on `Type` is deprecated. If for detection, use `Base.isType(x)`.", :nameof)
    return :Type
end

```
-/
def nameof_TypeEq {X : Type} (_x : X) : M World Sym := do
  depwarn_if_not_pure ops "calling `nameof` on `Type` is deprecated. If for detection, use `Base.isType(x)`." (.sym "nameof")
  return "Type"
/--
Julia source: base/deprecated.jl:660-664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function parentmodule(x::TypeEq)
    depwarn_if_not_pure("calling `parentmodule` on `Type` is deprecated. If for detection, use `Base.isType(x)`.", :parentmodule)
    return Core
end

```
-/
def parentmodule_TypeEq {X : Type} (_x : X) : M World Mod := do
  depwarn_if_not_pure ops "calling `parentmodule` on `Type` is deprecated. If for detection, use `Base.isType(x)`." (.sym "parentmodule")
  return ops.core
/--
Julia source: base/deprecated.jl:665-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function isabstracttype(x::TypeEq)
    depwarn_if_not_pure("calling `isabstracttype` on a `Type{...}` is deprecated; `Type{}` is now a kind. If for detection, use `Base.isType(x)`.", :isabstracttype)
    return true
end

```
-/
def isabstracttype_TypeEq {X : Type} (_x : X) : M World Bool := do
  depwarn_if_not_pure ops "calling `isabstracttype` on a `Type{...}` is deprecated; `Type{}` is now a kind. If for detection, use `Base.isType(x)`." (.sym "isabstracttype")
  return true
/--
Julia source: base/deprecated.jl:670-683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function getproperty(x::Core.TypeEgal, s::Symbol)
    if s === :parameters
        depwarn_if_not_pure("accessing `Type.parameters` is deprecated; use `Base.type_parameter(x)` instead", :getproperty)
        return Core.svec(type_parameter(x))
    elseif s === :name
        depwarn_if_not_pure("accessing `Type.name` is deprecated without replacement. If for detection, use `Base.isType(x)`.", :getproperty)
        return Core.AnyType.name
    elseif s === :hash
        depwarn_if_not_pure("accessing `Type.hash` is deprecated; use `Base._jl_type_hash(x)` instead", :getproperty)
        return reinterpret(Int32, UInt32(_jl_type_hash(x)))
    end
    return getfield(x, s)
end

```
-/
def getproperty_TypeEgal {X V : Type} (tops : TypePropertyOps World X V) (x : X) (s : Sym) : M World V := do
  if s == "parameters" then
    depwarn_if_not_pure ops "accessing `Type.parameters` is deprecated; use `Base.type_parameter(x)` instead" (.sym "getproperty")
    return (← tops.svecTypeParameter x)
  else if s == "name" then
    depwarn_if_not_pure ops "accessing `Type.name` is deprecated without replacement. If for detection, use `Base.isType(x)`." (.sym "getproperty")
    return tops.anyTypeName
  else if s == "hash" then
    depwarn_if_not_pure ops "accessing `Type.hash` is deprecated; use `Base._jl_type_hash(x)` instead" (.sym "getproperty")
    return tops.ofInt32 (← hashInt32 (← tops.typeHash x))
  tops.getfield x s
/--
Julia source: base/deprecated.jl:684-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function typename(x::Core.TypeEgal)
    depwarn_if_not_pure("calling `typename` on `Type` is deprecated. If for detection, use `Base.isType(x)`.", :typename)
    return Core.AnyType.name
end

```
-/
def typename_TypeEgal {X V : Type} (tops : TypePropertyOps World X V) (_x : X) : M World V := do
  depwarn_if_not_pure ops "calling `typename` on `Type` is deprecated. If for detection, use `Base.isType(x)`." (.sym "typename")
  return tops.anyTypeName
/--
Julia source: base/deprecated.jl:689-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function nameof(x::Core.TypeEgal)
    depwarn_if_not_pure("calling `nameof` on `Type` is deprecated. If for detection, use `Base.isType(x)`.", :nameof)
    return :Type
end

```
-/
def nameof_TypeEgal {X : Type} (_x : X) : M World Sym := do
  depwarn_if_not_pure ops "calling `nameof` on `Type` is deprecated. If for detection, use `Base.isType(x)`." (.sym "nameof")
  return "Type"
/--
Julia source: base/deprecated.jl:694-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function parentmodule(x::Core.TypeEgal)
    depwarn_if_not_pure("calling `parentmodule` on `Type` is deprecated. If for detection, use `Base.isType(x)`.", :parentmodule)
    return Core
end

```
-/
def parentmodule_TypeEgal {X : Type} (_x : X) : M World Mod := do
  depwarn_if_not_pure ops "calling `parentmodule` on `Type` is deprecated. If for detection, use `Base.isType(x)`." (.sym "parentmodule")
  return ops.core
/--
Julia source: base/deprecated.jl:699-703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function isabstracttype(x::Core.TypeEgal)
    depwarn_if_not_pure("calling `isabstracttype` on a `Type{...}` is deprecated; `Type{}` is now a kind. If for detection, use `Base.isType(x)`.", :isabstracttype)
    return true
end

```
-/
def isabstracttype_TypeEgal {X : Type} (_x : X) : M World Bool := do
  depwarn_if_not_pure ops "calling `isabstracttype` on a `Type{...}` is deprecated; `Type{}` is now a kind. If for detection, use `Base.isType(x)`." (.sym "isabstracttype")
  return true
/--
Julia source: base/deprecated.jl:704-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate SubString{T}(s::T, i::Int, j::Int, ::Val{:noshift}) where {T <: AbstractString} begin
    @boundscheck if !(i == j == 0)
        si, sj = i + 1, prevind(s, j + i + 1)
        @inbounds isvalid(s, si) || string_index_err(s, si)
        @inbounds isvalid(s, sj) || string_index_err(s, sj)
    end
    @inbounds raw_substring(s, i + 1, j)
end

# This method is slightly different because it returns a SubString{SubString},
# therefore it requires an explicit SubString{T}(ss) call at the end.
# We discourage creating substrings of substrings, but the deprecated method
# allowed it.
```
-/
-- The `@boundscheck` block of the deprecated `SubString{T}(s, i, j, Val(:noshift))`; `boundscheck`
-- is whether bounds checks run (they are elided only under `--check-bounds=no`).
def noshift_check {S SS : Type} (sops : SubStringOps World S SS) (boundscheck : Bool) (s : S)
    (i j : JInt64) : M World Unit := do
  if boundscheck then
    if !(i.val == j.val && j.val == 0) then
      let si := i + i64 1
      let sj ← sops.prevind s (j + i + i64 1)
      if !(← sops.isvalid s si) then sops.string_index_err s si
      if !(← sops.isvalid s sj) then sops.string_index_err s sj

/-- `SubString{T}(s::T, i::Int, j::Int, ::Val{:noshift}) where {T <: AbstractString}`. -/
def SubString_noshift {S SS : Type} (sops : SubStringOps World S SS) (boundscheck : Bool) (s : S)
    (i j : JInt64) : M World SS := do
  depwarn ops ("`SubString{T}(s::T, i::Int, j::Int, ::Val{:noshift}) where T <: AbstractString` is deprecated, use `begin\n" ++
    "    #= deprecated.jl:705 =# @boundscheck if !(i == j == 0)\n" ++
    "            (si, sj) = (i + 1, prevind(s, j + i + 1))\n" ++
    "            #= deprecated.jl:707 =# @inbounds isvalid(s, si) || string_index_err(s, si)\n" ++
    "            #= deprecated.jl:708 =# @inbounds isvalid(s, sj) || string_index_err(s, sj)\n" ++
    "        end\n" ++
    "    #= deprecated.jl:710 =# @inbounds raw_substring(s, i + 1, j)\n" ++
    "end` instead.") (.sym "AnyType")
  noshift_check sops boundscheck s i j
  sops.raw_substring s (i + i64 1) j
/--
Julia source: base/deprecated.jl:717-726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate SubString{T}(s::T, i::Int, j::Int, ::Val{:noshift}) where {T <: SubString} begin
    @boundscheck if !(i == j == 0)
        si, sj = i + 1, prevind(s, j + i + 1)
        @inbounds isvalid(s, si) || string_index_err(s, si)
        @inbounds isvalid(s, sj) || string_index_err(s, sj)
    end
    ss = @inbounds raw_substring(s, i + 1, j)
    SubString{T}(ss)
end

```
-/
def SubString_noshift_SubString {S SS R : Type} (sops : SubStringOps World S SS) (SubStringT : SS → M World R)
    (boundscheck : Bool) (s : S) (i j : JInt64) : M World R := do
  depwarn ops ("`SubString{T}(s::T, i::Int, j::Int, ::Val{:noshift}) where T <: SubString` is deprecated, use `begin\n" ++
    "    #= deprecated.jl:718 =# @boundscheck if !(i == j == 0)\n" ++
    "            (si, sj) = (i + 1, prevind(s, j + i + 1))\n" ++
    "            #= deprecated.jl:720 =# @inbounds isvalid(s, si) || string_index_err(s, si)\n" ++
    "            #= deprecated.jl:721 =# @inbounds isvalid(s, sj) || string_index_err(s, sj)\n" ++
    "        end\n" ++
    "    ss = #= deprecated.jl:723 =# @inbounds(raw_substring(s, i + 1, j))\n" ++
    "    SubString{T}(ss)\n" ++
    "end` instead.") (.sym "AnyType")
  noshift_check sops boundscheck s i j
  let ss ← sops.raw_substring s (i + i64 1) j
  SubStringT ss
/--
Julia source: base/deprecated.jl:727-727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate _unsetindex!(A) Base.unsetindex!(A) false
```
-/
def _unsetindex!_1 {A R : Type} (unsetindex! : A → M World R) (A' : A) : M World R := do
  depwarn ops "`_unsetindex!(A)` is deprecated, use `Base.unsetindex!(A)` instead." (.sym "_unsetindex!")
  unsetindex! A'
/--
Julia source: base/deprecated.jl:728-735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@deprecate _unsetindex!(A, i) Base.unsetindex!(A, i) false

# `a[] = v` on a `Threads.Atomic` (the `setindex!` form) is a footgun: read-modify-write
# expressions such as `a[] += 1` look atomic but expand to a separate non-atomic load and
# store. Steer users to the explicit `@atomic` form. This is written by hand rather than
# with `@deprecate` so the message can name the hazard and avoid the macro-expansion
# artifact `@deprecate` would embed in the suggested replacement.
# ## This is not yet enabled (deprecated) due to the need to transition a couple stdlibs to this form (or another equivalent form).
```
-/
def _unsetindex!_2 {A I R : Type} (unsetindex! : A → I → M World R) (A' : A) (i : I) : M World R := do
  depwarn ops "`_unsetindex!(A, i)` is deprecated, use `Base.unsetindex!(A, i)` instead." (.sym "_unsetindex!")
  unsetindex! A' i

end
/--
Julia source: base/deprecated.jl:736-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(x::Threads.Atomic, v)
    # depwarn(lazy"`a[] = v` on a `Threads.Atomic` is deprecated because read-modify-write uses like `a[] += 1` are not atomic; use `@atomic a[] = v` (or `@atomic a[] += 1`, `Threads.atomic_add!`, ...) instead.", :setindex!)
    return @atomic x[] = v
end

# The `*_domain_error` helpers were replaced by `Math.throw_finite_domainerror` in #62842,
# but some packages call them directly. Not deprecated, just kept for compatibility.
```
-/
-- `setindex!(x::Threads.Atomic, v)`; `atomicStore` is `@atomic x[] = v`.
def setindex!_Atomic {World A V : Type} (atomicStore : A → V → M World V) (x : A) (v : V) : M World V :=
  atomicStore x v
/--
Julia source: base/deprecated.jl:743-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval Math begin
    @noinline sin_domain_error(x) = throw_finite_domainerror(:sin, x)
    @noinline cos_domain_error(x) = throw_finite_domainerror(:cos, x)
    @noinline sincos_domain_error(x) = throw_finite_domainerror(:sincos, x)
    @noinline tan_domain_error(x) = throw_finite_domainerror(:tan, x)
end

# END 1.14 deprecations
```
-/
def sin_domain_error {World X R : Type} (throw_finite_domainerror : Sym → X → M World R) (x : X) : M World R :=
  throw_finite_domainerror "sin" x
def cos_domain_error {World X R : Type} (throw_finite_domainerror : Sym → X → M World R) (x : X) : M World R :=
  throw_finite_domainerror "cos" x
def sincos_domain_error {World X R : Type} (throw_finite_domainerror : Sym → X → M World R) (x : X) : M World R :=
  throw_finite_domainerror "sincos" x
def tan_domain_error {World X R : Type} (throw_finite_domainerror : Sym → X → M World R) (x : X) : M World R :=
  throw_finite_domainerror "tan" x

end JuliaLean.base.deprecated

namespace JuliaLean.MemSafety.G1

open JuliaLean

/-- The first deprecated method at `base/deprecated.jl:704-710`. The old
arguments are a zero-based offset and a signed code-unit count. It computes both
endpoints, validates them, and calls `raw_substring` with bounds checks removed. -/
def deprecatedNoshiftString (s : Strings.JStr) (i n : JInt64) : Strings.SJl Strings.JSub :=
  let first := i + Strings.ix 1
  if !(decide (i.val = 0) && decide (n.val = 0)) then
    match Strings.prevind s (n + i + Strings.ix 1) with
    | .error e => .error e
    | .ok last =>
      if !Strings.isvalidAt s first then .error (.stringIndexError first.val)
      else if !Strings.isvalidAt s last then .error (.stringIndexError last.val)
      else Strings.rawSubstring s first n false
  else Strings.rawSubstring s first n false

/-- The second deprecated method at `base/deprecated.jl:717-723`, through the
unchecked `raw_substring` call. `SubString{T}(ss)` after that call only wraps
the returned view and cannot repair an invalid offset or count. -/
def deprecatedNoshiftSubString (s : Strings.JSub) (i n : JInt64) : Strings.SJl Strings.JSub :=
  let first := i + Strings.ix 1
  let localView := s.view
  if !(decide (i.val = 0) && decide (n.val = 0)) then
    match Strings.prevind localView (n + i + Strings.ix 1) with
    | .error e => .error e
    | .ok last =>
      if !Strings.isvalidAt localView first then .error (.stringIndexError first.val)
      else if !Strings.isvalidAt localView last then .error (.stringIndexError last.val)
      else Strings.rawSubstring s.str (first + s.offset) n false
  else Strings.rawSubstring s.str (first + s.offset) n false

end JuliaLean.MemSafety.G1

namespace JuliaLean.MiscCov.Deprecated

open JuliaLean.MiscCov
/-! ## `__has_internal_change`, `base/deprecated.jl:110-113` -/

/-- `__has_internal_change(version_or, change_name)`: `vgt` is `VERSION > version_or`. -/
def hasInternalChange (vgt : Bool) (changes : List String) (name : String) : Bool :=
  if vgt then true else changes.contains name


/-! ## `@deprecate`, `base/deprecated.jl:179-231` -/

/-- The error of `cannot_export_nonsymbol()`, `base/deprecated.jl:180-188`. -/
def cannotExportMsg : String :=
  "if the third `export_old` argument is not specified or `true`, the first argument must be of form (1) `f(...)` where `f` is a symbol, (2) `T{...}(...)` where `T` is a symbol, or (3) a symbol."

def cannotExportNonsymbol {α : Type} : M α := .error (.errorException cannotExportMsg)

/-- `Core.Typeof($(esc(f))).name.singletonname`. -/
def singletonName (f : Ex) : Ex :=
  .expr "." [.expr "." [.expr "call" [.gref "Core" "Typeof", Ex.esc f], .qn (.sym "name")], .qn (.sym "singletonname")]

/-- `@deprecate old new export_old`, `base/deprecated.jl:179-231`. -/
def deprecate (shw : Ex → String) (old new : Ex) (exportOld : Bool) : M Ex := do
  let metaEx := Ex.expr "meta" [.sym "noinline"]
  match old with
  | .expr h oargs =>
    if h = "call" ∨ h = "where" then do
      let new := removeLinenums new
      let oldcall := shw old
      let newcall := shw new
      let callexpr ← (if h = "call" then pure old else
        match oargs with
        | c :: _ => pure c
        | [] => .error .boundsError : M Ex)
      match callexpr with
      | .expr "call" (fn0 :: _) =>
        let fnexpr := match fn0 with
          | .expr "curly" (t :: _) => t
          | _ => fn0
        let maybeExport ← (if exportOld then
            match fnexpr with
            | .sym _ => pure (Ex.expr "export" [Ex.esc fnexpr])
            | _ => cannotExportNonsymbol
          else pure .nothing : M Ex)
        let ex := Ex.expr "=" [Ex.esc old, .expr "block" [metaEx,
          .expr "call" [.sym "depwarn", .str ("`" ++ oldcall ++ "` is deprecated, use `" ++ newcall ++ "` instead."),
            singletonName fnexpr], Ex.esc new]]
        pure (.expr "toplevel" [maybeExport, replaceLinenums ex])
      | .expr "call" [] => .error .boundsError
      | .expr _ _ => .error (.errorException "invalid usage of @deprecate")
      | _ => .error .fieldError
    else deprecateOther shw old new exportOld metaEx
  | _ => deprecateOther shw old new exportOld metaEx
where
  /-- The `else` branch, `base/deprecated.jl:219-229`, and the generated method
  `$(esc(old))(args...; kwargs...)` (`base/deprecated.jl:222-226`). -/
  deprecateOther (shw : Ex → String) (old new : Ex) (exportOld : Bool) (metaEx : Ex) : M Ex :=
    if exportOld && !(match old with | .sym _ => true | _ => false) then cannotExportNonsymbol
    else
      let ex := Ex.expr "function" [.expr "call" [Ex.esc old, .expr "parameters" [.expr "..." [.sym "kwargs"]],
          .expr "..." [.sym "args"]],
        .expr "block" [metaEx,
          .expr "call" [.sym "depwarn", .str ("`" ++ shw old ++ "` is deprecated, use `" ++ shw new ++ "` instead."),
            singletonName old],
          .expr "call" [Ex.esc new, .expr "parameters" [.expr "..." [.sym "kwargs"]], .expr "..." [.sym "args"]]]]
      .ok (.expr "toplevel" [if exportOld then .expr "export" [Ex.esc old] else .nothing, replaceLinenums ex])


/-! ## `depwarn`, `base/deprecated.jl:253-317` -/

/-- One `StackTraces.lookup` result: the function name, whether it is a C frame or
`StackTraces.UNKNOWN`, and the name of the method of its `MethodInstance` if any. -/
structure Frame where
  func : String
  fromC : Bool
  unknown : Bool
  methodName : Option String
  deriving DecidableEq, Repr

/-- A backtrace: each instruction pointer with its inlined frames. -/
abbrev Backtrace := List (Nat × List Frame)

/-- The result of `firstcaller`: the instruction pointer and the frame, `none` for
`StackTraces.UNKNOWN`. -/
abbrev Caller := Nat × Option Frame

/-- The search of `firstcaller(bt, funcsyms)`, `base/deprecated.jl:293-317`: `found`
carries over from one frame to the next. -/
def firstcallerLoop (funcsyms : List String) : Bool → Backtrace → Caller
  | _, [] => (0, none)
  | found, (ip, lkups) :: bt =>
    let rec inner : Bool → List Frame → Sum Caller Bool
      | found, [] => .inr found
      | found, l :: ls =>
        if l.unknown || l.fromC then inner found ls
        else if found then .inl (ip, some l)
        else
          let found := funcsyms.contains l.func ||
            (match l.methodName with | some n => funcsyms.contains n | none => false)
          inner found ls
    match inner found lkups with
    | .inl c => c
    | .inr found => firstcallerLoop funcsyms found bt

/-- `firstcaller(bt, funcsyms)`, `base/deprecated.jl:293-317`. -/
def firstcallerTuple (bt : Backtrace) (funcsyms : List String) : Caller := firstcallerLoop funcsyms false bt

/-- `firstcaller(bt, ::Nothing)`, `base/deprecated.jl:291`. -/
def firstcallerNothing (_bt : Backtrace) : Caller := (0, none)

/-- `firstcaller(bt, funcsym::Symbol)`, `base/deprecated.jl:292`. -/
def firstcallerSym (bt : Backtrace) (funcsym : String) : Caller := firstcallerTuple bt [funcsym]

/-- A log record written by `@logmsg`: level (`true` is `Warn`, `false` is
`BelowMinLevel`), message, `_id = (frame, funcsym)`, `_group = :depwarn` and `maxlog`. -/
structure LogRec where
  warn : Bool
  msg : String
  id : Nat × Option String
  caller : Option Frame
  maxlog : Option Nat
  deriving DecidableEq, Repr

/-- `_depwarn(msg, funcsym, force)`, `base/deprecated.jl:260-289`. `level` is
`JLOptions().depwarn`. -/
def depwarnImpl (level : Nat) (bt : Backtrace) (msg : String) (funcsym : Option String) (force : Bool) :
    M (Option LogRec) :=
  if level = 2 then .error (.errorException msg)
  else
    let warn := force || level == 1
    let (frame, caller) := match funcsym with
      | none => firstcallerNothing bt
      | some f => firstcallerSym bt f
    .ok (some ⟨warn, msg, (frame, funcsym), caller, if funcsym.isNone then none else some 1⟩)

/-- `depwarn(msg, funcsym; force=false)`, `base/deprecated.jl:253-259`: `_depwarn` called
through `@invokelatest`. -/
def depwarn (level : Nat) (bt : Backtrace) (msg : String) (funcsym : Option String) (force : Bool := false) :
    M (Option LogRec) :=
  depwarnImpl level bt msg funcsym force



/-! ## Binding deprecations, `base/deprecated.jl:319-376` -/

/-- `deprecate(m, s, flag)`, `base/deprecated.jl:319`: `jl_deprecate_binding` sets the
deprecation flag of binding `m.s`. The table maps bindings to flags. -/
def deprecateBinding (tab : List ((String × String) × Nat)) (m s : String) (flag : Nat := 1) :
    List ((String × String) × Nat) :=
  ((m, s), flag) :: tab.filter (fun e => e.1 != (m, s))

/-- The flag of a binding (`0`: not deprecated). -/
def flagOf (tab : List ((String × String) × Nat)) (m s : String) : Nat :=
  ((tab.find? (fun e => e.1 == (m, s))).map (·.2)).getD 0

/-- `@deprecate_binding old new export_old dep_message constant`,
`base/deprecated.jl:346-353`; `dep_message = none` is `:nothing`. -/
def deprecateBindingMacro (str : Ex → String) (mod : String) (old new : Ex) (exportOld : Bool := true)
    (depMessage : Option Ex := none) (constant : Bool := true) : Ex :=
  let depMessage := depMessage.getD (.str (", use " ++ str new ++ " instead."))
  .expr "toplevel" [if exportOld then .expr "export" [Ex.esc old] else .nothing,
    .expr "const" [.expr "=" [Ex.esc (.sym ("_dep_message_" ++ str old)), Ex.esc depMessage]],
    if constant then .expr "const" [.expr "=" [Ex.esc old, Ex.esc new]] else .expr "=" [Ex.esc old, Ex.esc new],
    .expr "call" [.sym "deprecate", .val mod, .expr "quote" [old]]]

/-- `@deprecate_stdlib old mod export_old newname`, `base/deprecated.jl:355-365`.
`root` is `Base.root_module(Base, mod)`, which throws for a module not loaded. -/
def deprecateStdlib (str : Ex → String) (root : Ex → M String) (cur : String) (old mod : Ex)
    (exportOld : Bool := true) (newname : Ex := old) : M Ex := do
  let rename := if str old = str newname then "" else " as `" ++ str newname ++ "`"
  let depMessage := ": it has been moved to the standard library package `" ++ str mod ++ "`" ++ rename ++
    ".\nAdd `using " ++ str mod ++ "` to your imports."
  let m ← root mod
  let new := Ex.gref m (str newname)
  pure (.expr "toplevel" [if exportOld then .expr "export" [Ex.esc old] else .nothing,
    .expr "const" [.expr "=" [Ex.esc (.sym ("_dep_message_" ++ str old)), Ex.esc (.str depMessage)]],
    .expr "const" [.expr "=" [Ex.esc old, Ex.esc new]],
    .expr "call" [.sym "deprecate", .val cur, .expr "quote" [old]]])

/-- `@deprecate_moved old new export_old`, `base/deprecated.jl:367-376`, including the
generated `$eold(args...; kwargs...) = error($emsg)` (`:373`). -/
def deprecateMoved (str : Ex → String) (cur : String) (old new : Ex) (exportOld : Bool := true) : Ex :=
  let emsg := str old ++ " has been moved to the package " ++ str new ++ ".jl.\n" ++
    "Run `Pkg.add(\"" ++ str new ++ "\")` to install it, restart Julia,\n" ++
    "and then run `using " ++ str new ++ "` to load it."
  .expr "toplevel" [
    replaceLinenums (.expr "=" [.expr "call" [Ex.esc old, .expr "parameters" [.expr "..." [.sym "kwargs"]],
      .expr "..." [.sym "args"]], .expr "call" [.sym "error", .str emsg]]),
    if exportOld then .expr "export" [Ex.esc old] else .nothing,
    .expr "call" [.sym "deprecate", .val cur, .expr "quote" [old], .int 2]]

end JuliaLean.MiscCov.Deprecated
