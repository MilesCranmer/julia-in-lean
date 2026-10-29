import JuliaLean.Core

/-!
# Model of `base/strings/lazy.jl`

Parts are an ordered list of existentially typed values, so Julia's heterogeneous tuple is kept
heterogeneous. The printer is a typed parameter for each captured value. Eager strings are byte
sequences, and the cache transition returned by `toString` models the mutable `str` field.
-/

namespace JuliaLean.base.strings.lazy

open JuliaLean

abbrev Index := JInt64
abbrev EagerString := List UInt8
abbrev LazyPart := Σ α : Type, α

structure PrintContext where
  compact : Bool
  limit : Bool
  deriving DecidableEq, Repr

abbrev ValuePrinter (E : Type) := {α : Type} → α → PrintContext → Except E EagerString

/--
Julia source: base/strings/lazy.jl:1-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    LazyString <: AbstractString

A lazy representation of string interpolation. This is useful when a string
needs to be constructed in a context where performing the actual interpolation
and string construction is unnecessary or undesirable (e.g. in error paths
of functions).

This type is designed to be cheap to construct at runtime, trying to offload
as much work as possible to either the macro or later printing operations.

# Examples

```jldoctest
julia> n = 5; str = LazyString("n is ", n)
"n is 5"
```

See also [`@lazy_str`](@ref).

!!! compat "Julia 1.8"
    `LazyString` requires Julia 1.8 or later.

# Extended help
## Safety properties for concurrent programs

A lazy string itself does not introduce any concurrency problems even if it is printed in
multiple Julia tasks.  However, if `print` methods on a captured value can have a
concurrency issue when invoked without synchronizations, printing the lazy string may cause
an issue.  Furthermore, the `print` methods on the captured values may be invoked multiple
times, though only exactly one result will be returned.

!!! compat "Julia 1.9"
    `LazyString` is safe in the above sense in Julia 1.9 and later.
"""
````
Julia source: base/strings/lazy.jl:36-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct LazyString <: AbstractString
    const parts::Tuple
    const compact::Bool # compact & limited output
    # Created on first access
    @atomic str::Union{String,Nothing}
    global _LazyString(parts, str) = new(parts, false, str)
    LazyString(args...; compact::Bool=false) = new(args, compact, nothing)
end

```
-/
structure LazyString where
  parts : List LazyPart
  compact : Bool
  str : Option EagerString

structure AtomicReplaceResult where
  old : EagerString
  ok : Bool

abbrev AtomicReplace := LazyString → EagerString → AtomicReplaceResult

inductive CodeUnitKind where
  | uint8 | uint16 | uint32
  deriving DecidableEq, Repr

inductive MacroExpr where
  | text (bytes : EagerString)
  | escaped (expression : MacroExpr)
  | lazyString (parts : List MacroExpr) (compact : Bool)
  deriving Repr

/-- The typed Julia `print(value, io)` dispatch for one heterogeneously typed part. -/
def printPart {E : Type} (print : ValuePrinter E) (context : PrintContext)
    (part : LazyPart) : Except E EagerString :=
  match part with
  | ⟨_, value⟩ => print value context

/-- Julia's left-to-right `foreach(print, parts)` output. -/
def printParts {E : Type} (print : ValuePrinter E) (context : PrintContext) :
    List LazyPart → Except E EagerString
  | [] => .ok []
  | part :: rest => do
      let first ← printPart print context part
      let remaining ← printParts print context rest
      pure (first ++ remaining)

/-- Eager byte concatenation, stated independently of the source loop in `String`. -/
def eagerString {E : Type} (print : ValuePrinter E) (context : PrintContext)
    (parts : List LazyPart) : Except E EagerString := do
  let chunks ← parts.mapM (printPart print context)
  pure chunks.flatten

/-- Julia's compact and limited `IOContext` selected by `lazy"..."c`. -/
def compactContext : PrintContext := ⟨true, true⟩

/-- Julia's ordinary `sprint` context. -/
def ordinaryContext : PrintContext := ⟨false, false⟩

/-- One-based increment of an `Int` index. -/
def nextIndex (i : Index) : Index := i + JInt.lit .i64 1

/-- Julia's byte index `1` on the 64-bit target. -/
def firstIndex : Index := JInt.lit .i64 1

/-- `Macro.parseatom` result with its exact returned expression and source index. -/
abbrev ParsedAtom := MacroExpr × Index

partial def lazyLoop {E : Type}
    (findnext : Char → EagerString → Index → Option Index)
    (prevind : EagerString → Index → Index)
    (lastindex : EagerString → Index)
    (slice : EagerString → Index → Index → EagerString)
    (parseatom : EagerString → Index → String → Except E ParsedAtom)
    (sourceFile : String) (text : EagerString) (idx lastidx : Index)
    (parts : List MacroExpr) : Except E (List MacroExpr) := do
  match findnext '$' text idx with
  | none =>
      if lastidx ≤ lastindex text then
        pure (parts ++ [.text (slice text lastidx (lastindex text))])
      else
        pure parts
  | some dollarIndex =>
      let parts :=
        if lastidx < dollarIndex then
          parts ++ [.text (slice text lastidx (prevind text dollarIndex))]
        else
          parts
      let idx := nextIndex dollarIndex
      let (expression, idx) ← parseatom text idx sourceFile
      let parts := parts ++ [.escaped expression]
      let lastidx := idx
      lazyLoop findnext prevind lastindex slice parseatom sourceFile text idx lastidx parts

/--
Julia source: base/strings/lazy.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global _LazyString(parts, str) = new(parts, false, str)
```
-/
def _LazyString {P S E : Type} (convertParts : P → Except E (List LazyPart))
    (convertCache : S → Except E (Option EagerString)) (parts : P) (str : S) :
    Except E LazyString :=
  match convertParts parts with
  | .error error => .error error
  | .ok parts =>
      match convertCache str with
      | .error error => .error error
      | .ok str => .ok ⟨parts, false, str⟩

/--
Julia source: base/strings/lazy.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    LazyString(args...; compact::Bool=false) = new(args, compact, nothing)
```
-/
def lazyStringCtor (args : List LazyPart) (compact : Bool := false) : LazyString :=
  ⟨args, compact, none⟩

/--
Julia source: base/strings/lazy.jl:45-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    lazy"str"
    lazy"str"c

Create a [`LazyString`](@ref) using regular string interpolation syntax.
Note that interpolations are *evaluated* at LazyString construction time,
but *printing* is delayed until the first access to the string.  The `lazy"str"c`
variant uses an [`IOContext`](@ref) with `:compact=>true, :limit=>true` when
printing, in order to keep the output string compact.

See [`LazyString`](@ref) documentation for the safety properties for concurrent programs.

# Examples

```
julia> n = 5; str = lazy"n is \$n"
"n is 5"

julia> typeof(str)
LazyString
```

!!! compat "Julia 1.8"
    `lazy"str"` requires Julia 1.8 or later.

!!! compat "Julia 1.14"
    `lazy"str"c` requires Julia 1.14 or later.
"""
macro lazy_str(text, flags...)
    compact = flags == ("c",)
    isempty(flags) || compact || throw(ArgumentError("unknown lazy-string flag: $flags"))
    parts = Any[]
    lastidx = idx = 1
    while (idx = findnext('$', text, idx)) !== nothing
        lastidx < idx && push!(parts, text[lastidx:prevind(text, idx)])
        idx += 1
        expr, idx = Meta.parseatom(text, idx; filename=string(__source__.file))
        push!(parts, esc(expr))
        lastidx = idx
    end
    lastidx <= lastindex(text) && push!(parts, text[lastidx:end])
    :(LazyString($(parts...); compact=$compact))
end

````
-/
def lazy_str {E : Type}
    (findnext : Char → EagerString → Index → Option Index)
    (prevind : EagerString → Index → Index)
    (lastindex : EagerString → Index)
    (slice : EagerString → Index → Index → EagerString)
    (parseatom : EagerString → Index → String → Except E ParsedAtom)
    (showFlags : List String → String)
    (argumentError : String → E)
    (sourceFile : String) (text : EagerString) (flags : List String) : Except E MacroExpr := do
  let compact := flags == ["c"]
  if flags.isEmpty || compact then
    let parts ← lazyLoop findnext prevind lastindex slice parseatom sourceFile text
      firstIndex firstIndex []
    pure (.lazyString parts compact)
  else
    .error (argumentError ("unknown lazy-string flag: " ++ showFlags flags))

/--
Julia source: base/strings/lazy.jl:89-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function String(l::LazyString)
    old = @atomic :acquire l.str
    old === nothing || return old
    str = sprint() do io
        if l.compact
            foreach(Fix1(print, IOContext(io, :compact=>true, :limit=>true)), l.parts)
        else
            foreach(Fix1(print, io), l.parts)
        end
    end
    old, ok = @atomicreplace :acquire_release :acquire l.str nothing => str
    return ok ? str : (old::String)
end

```
-/
def toString {E : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (l : LazyString) : Except E (LazyString × EagerString) :=
  match l.str with
  | some cached => .ok (l, cached)
  | none =>
      match (if l.compact then printParts print compactContext l.parts
          else printParts print ordinaryContext l.parts) with
      | .error error => .error error
      | .ok str =>
          let replacement := atomicReplace l str
          let old := replacement.old
          let ok := replacement.ok
          let result := if ok then str else old
          .ok ({ l with str := some result }, result)

/--
Julia source: base/strings/lazy.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(s::LazyString, h::UInt64) = hash(String(s), h)
```
-/
def hash {E : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringHash : EagerString → UInt64 → UInt64) (s : LazyString) (h : UInt64) :
    Except E (LazyString × UInt64) := do
  let (s, str) ← toString print atomicReplace s
  pure (s, stringHash str h)

/--
Julia source: base/strings/lazy.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(s::LazyString) = lastindex(String(s))
```
-/
def lastindex {E : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringLastindex : EagerString → Index) (s : LazyString) :
    Except E (LazyString × Index) := do
  let (s, str) ← toString print atomicReplace s
  pure (s, stringLastindex str)

/--
Julia source: base/strings/lazy.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(s::LazyString) = iterate(String(s))
```
-/
def iterate0 {E : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringIterate : EagerString → Except E (Option (UInt32 × Index))) (s : LazyString) :
    Except E (LazyString × Option (UInt32 × Index)) :=
  match toString print atomicReplace s with
  | .error error => .error error
  | .ok (s, str) =>
      match stringIterate str with
      | .error error => .error error
      | .ok next => .ok (s, next)

/--
Julia source: base/strings/lazy.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(s::LazyString, i::Integer) = iterate(String(s), i)
```
-/
def iterateAt {E I : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringIterate : EagerString → I → Except E (Option (UInt32 × Index)))
    (s : LazyString) (i : I) : Except E (LazyString × Option (UInt32 × Index)) :=
  match toString print atomicReplace s with
  | .error error => .error error
  | .ok (s, str) =>
      match stringIterate str i with
      | .error error => .error error
      | .ok next => .ok (s, next)

/--
Julia source: base/strings/lazy.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(a::LazyString, b::LazyString) = isequal(String(a), String(b))
```
-/
def isequal {E : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringIsequal : EagerString → EagerString → Bool) (a b : LazyString) :
    Except E (LazyString × LazyString × Bool) := do
  let (a, stringA) ← toString print atomicReplace a
  let (b, stringB) ← toString print atomicReplace b
  pure (a, b, stringIsequal stringA stringB)

/--
Julia source: base/strings/lazy.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::LazyString, b::LazyString) = (String(a) == String(b))
```
-/
def eq {E : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringEq : EagerString → EagerString → Bool) (a b : LazyString) :
    Except E (LazyString × LazyString × Bool) := do
  let (a, stringA) ← toString print atomicReplace a
  let (b, stringB) ← toString print atomicReplace b
  pure (a, b, stringEq stringA stringB)

/--
Julia source: base/strings/lazy.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(s::LazyString) = ncodeunits(String(s))
```
-/
def ncodeunits {E : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringNcodeunits : EagerString → Index) (s : LazyString) :
    Except E (LazyString × Index) := do
  let (s, str) ← toString print atomicReplace s
  pure (s, stringNcodeunits str)

/--
Julia source: base/strings/lazy.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::LazyString) = codeunit("") # returns UInt8
```
-/
def codeunitType (stringCodeunitType : EagerString → CodeUnitKind) (_s : LazyString) :
    CodeUnitKind :=
  stringCodeunitType []

/--
Julia source: base/strings/lazy.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::LazyString, i::Integer) = codeunit(String(s), i)
```
-/
def codeunitAt {E I : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringCodeunit : EagerString → I → Except E UInt8) (s : LazyString) (i : I) :
    Except E (LazyString × UInt8) :=
  match toString print atomicReplace s with
  | .error error => .error error
  | .ok (s, str) =>
      match stringCodeunit str i with
      | .error error => .error error
      | .ok byte => .ok (s, byte)

/--
Julia source: base/strings/lazy.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunits(s::LazyString) = codeunits(String(s))
```
-/
def codeunits {E R : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringCodeunits : EagerString → R) (s : LazyString) :
    Except E (LazyString × R) := do
  let (s, str) ← toString print atomicReplace s
  pure (s, stringCodeunits str)

/--
Julia source: base/strings/lazy.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(s::LazyString, i::Integer) = isvalid(String(s), i)
```
-/
def isvalid {E I : Type} (print : ValuePrinter E) (atomicReplace : AtomicReplace)
    (stringIsvalid : EagerString → I → Except E Bool) (s : LazyString) (i : I) :
    Except E (LazyString × Bool) :=
  match toString print atomicReplace s with
  | .error error => .error error
  | .ok (s, str) =>
      match stringIsvalid str i with
      | .error error => .error error
      | .ok valid => .ok (s, valid)

end JuliaLean.base.strings.lazy
