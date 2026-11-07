import JuliaLean.Core
import JuliaLean.base.expr


section

/-!
# `base/docs/core.jl`, `base/docs/utils.jl`, `base/docs/bindings.jl`, `base/docs/basedocs.jl`

Models of the bootstrap docsystem (`Core.CoreDocs`), the `HTML`/`Text` wrappers,
`Docs.Binding` and the `kw"..."` keyword literal, master `bbfa0ce4150`.
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## `base/docs/utils.jl` -/

/-- The content of an `HTML{T}` or `Text{T}`: a value printed with `print`, or a
function (`T <: Function`) that writes the given strings to the stream. -/
inductive Content (C : Type) where
  | value (c : C)
  | fn (out : List String)

/-- `HTML(xs...)`, `base/docs/utils.jl:33-39`: an `HTML` whose content function prints
each argument in turn. `printC` is `print` of one argument. -/
def htmlVarargs {C : Type} (printC : C → String) (xs : List C) : Content C :=
  .fn (xs.map printC)

/-- `show(io, MIME"text/html"(), h::HTML)` and `show(io, MIME"text/html"(), h::HTML{<:Function})`,
`base/docs/utils.jl:41-42`: the bytes written. -/
def showHtml {C : Type} (printC : C → String) : Content C → String
  | .value c => printC c
  | .fn out => String.join out

/-- `html"s"`, `base/docs/utils.jl:55-57`: `HTML(s)` of the string literal. -/
def htmlStr (s : String) : Content String := .value s

/-- `catdoc(xs::HTML...)`, `base/docs/utils.jl:59-65`: an `HTML` whose function shows
each part as `text/html`. -/
def catdocHtml {C : Type} (printC : C → String) (xs : List (Content C)) : Content C :=
  .fn (xs.map (showHtml printC))

/-- `print(io, t::Text)` and `print(io, t::Text{<:Function})`, `base/docs/utils.jl:91-92`. -/
def printText {C : Type} (printC : C → String) : Content C → String
  | .value c => printC c
  | .fn out => String.join out

/-- `show(io, t::Text) = print(io, t)`, `base/docs/utils.jl:93`. -/
def showText {C : Type} (printC : C → String) (t : Content C) : String := printText printC t

/-- `text"s"`, `base/docs/utils.jl:109-111`. -/
def textStr (s : String) : Content String := .value s

/-- `catdoc(xs::Text...)`, `base/docs/utils.jl:113-119`: each part is shown as
`text/plain`, which for `Text` falls back to `show(io, x)`. -/
def catdocText {C : Type} (printC : C → String) (xs : List (Content C)) : Content C :=
  .fn (xs.map (showText printC))

/-- Julia's `==`, `isequal` and `hash` of a content type `T` (`hash` on `UInt64`). -/
structure ContentOps (C : Type) where
  eq : C → C → Bool
  isequal : C → C → Bool
  hash : C → Nat → Nat
  /-- `hash(T, h)` of the wrapper type `HTML{T}`/`Text{T}`. -/
  hashType : Nat → Nat

/-- `==(t1::T, t2::T) where {T<:Union{HTML,Text}}`, `base/docs/utils.jl:95`, on value
contents of the same type. -/
def wrapperEq {C : Type} (ops : ContentOps C) (a b : C) : Bool := ops.eq a b

/-- `hash(t::T, h) where {T<:Union{HTML,Text}} = hash(T, hash(t.content, h))`,
`base/docs/utils.jl:96`. -/
def wrapperHash {C : Type} (ops : ContentOps C) (a : C) (h : Nat) : Nat :=
  ops.hashType (ops.hash a h)

/-- `isequal(t1, t2)` for `HTML`/`Text`: no method is defined, so Base's fallback
`isequal(x, y) = x == y` (`base/operators.jl`) applies. -/
def wrapperIsequal {C : Type} (ops : ContentOps C) (a b : C) : Bool := wrapperEq ops a b

end JuliaLean.DocsSyntaxCov

end


/-!
# Model of `base/docs/utils.jl`

Typed model of the `Docs.HTML` and `Docs.Text` wrappers at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Each modelled method is a Lean definition whose
docstring carries the method's verbatim source; its body follows the Julia body call by call.

* The `content` field is either a `Function`, which the printers call on the stream, or any
  other value, which they `print`. Output happens in a monad `m` over a stream type `Io`;
  `print(io, x)` of a content value and of each argument is a callee.
* The string macros return `Value L` expressions of the `base/expr.jl` model.
-/

namespace JuliaLean.base.docs.utils
open JuliaLean
open JuliaLean.base.expr (Value)

/-- The `content` of an `HTML{T}` or `Text{T}`: a `Function` (`T <: Function`) or another value. -/
inductive Content (n : Type → Type) (Io X : Type) where
  | func (f : Io → n Unit)
  | value (x : X)

-- UNTRANSLATED
-- license header, imports and exports; no method
-- Source: base/docs/utils.jl:1-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Text / HTML objects
-- 
-- import .Base: print, show, ==, hash
-- 
-- export HTML, @html_str
-- 
-- export HTML, Text
-- 
-- /Source

/--
Julia source: base/docs/utils.jl:11-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
`HTML(s)`: Create an object that renders `s` as html.

    HTML("<div>foo</div>")

You can also use a stream for large amounts of data:

    HTML() do io
      println(io, "<div>foo</div>")
    end

!!! warning
    `HTML` is currently exported to maintain
    backwards compatibility, but this export
    is deprecated. It is recommended to use
    this type as [`Docs.HTML`](@ref) or to explicitly
    import it from `Docs`.
"""
mutable struct HTML{T}
    content::T
end

```
-/
/- `HTML{T}`. -/
structure HTML (n : Type → Type) (Io X : Type) where
  content : Content n Io X

section
variable {m : Type → Type} [Monad m] {Io X : Type}

/--
Julia source: base/docs/utils.jl:33-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function HTML(xs...)
    HTML() do io
        for x in xs
            print(io, x)
        end
    end
end

```
-/
/- `HTML(xs...)` with zero or at least two arguments (one argument selects the default
constructor `HTML(content)`): the content is the closure printing each `x`. -/
def HTML_vararg (print : Io → X → m Unit) (xs : List X) : HTML m Io X :=
  ⟨.func fun io => do
    for x in xs do
      print io x⟩

/--
Julia source: base/docs/utils.jl:41-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/html", h::HTML) = print(io, h.content)
show(io::IO, ::MIME"text/html", h::HTML{<:Function}) = h.content(io)

```
-/
/- `show(io, ::MIME"text/html", h::HTML)`: Julia selects the `HTML{<:Function}` method for a
`Function` content. -/
def show_html (print : Io → X → m Unit) (io : Io) (h : HTML m Io X) : m Unit :=
  match h.content with
  | .func f => f io
  | .value x => print io x

end

/--
Julia source: base/docs/utils.jl:44-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @html_str -> Docs.HTML

Create an `HTML` object from a literal string.

# Examples
```jldoctest
julia> html"Julia"
HTML{String}("Julia")
```
"""
macro html_str(s)
    :(HTML($s))
end

````
-/
/- `@html_str(s)` returns `:(HTML($s))`. -/
def html_str {L : Type} (s : Value L) : Value L := .expr "call" [.symbol "HTML", s]

section
variable {m : Type → Type} [Monad m] {Io X : Type}

/--
Julia source: base/docs/utils.jl:59-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function catdoc(xs::HTML...)
    HTML() do io
        for x in xs
            show(io, MIME"text/html"(), x)
        end
    end
end

```
-/
/- `catdoc(xs::HTML...)`. -/
def catdoc_HTML {Y : Type} (print : Io → X → m Unit) (xs : List (HTML m Io X)) : HTML m Io Y :=
  ⟨.func fun io => do
    for x in xs do
      show_html print io x⟩

-- UNTRANSLATED
-- `export` statement; no method
-- Source: base/docs/utils.jl:67-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- export Text, @text_str
-- 
-- /Source

/--
Julia source: base/docs/utils.jl:69-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
`Text(s)`: Create an object that renders `s` as plain text.

    Text("foo")

You can also use a stream for large amounts of data:

    Text() do io
      println(io, "foo")
    end

!!! warning
    `Text` is currently exported to maintain
    backwards compatibility, but this export
    is deprecated. It is recommended to use
    this type as [`Docs.Text`](@ref) or to explicitly
    import it from `Docs`.
"""
mutable struct Text{T}
    content::T
end

```
-/
/- `Text{T}`. -/
structure Text (n : Type → Type) (Io X : Type) where
  content : Content n Io X

/--
Julia source: base/docs/utils.jl:91-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, t::Text) = print(io, t.content)
print(io::IO, t::Text{<:Function}) = t.content(io)
show(io::IO, t::Text) = print(io, t)

```
-/
/- `print(io, t::Text)`: Julia selects the `Text{<:Function}` method for a `Function` content. -/
def print_Text (print : Io → X → m Unit) (io : Io) (t : Text m Io X) : m Unit :=
  match t.content with
  | .func f => f io
  | .value x => print io x

/-- `show(io, t::Text) = print(io, t)`. -/
def show_Text (print : Io → X → m Unit) (io : Io) (t : Text m Io X) : m Unit := print_Text print io t

/--
Julia source: base/docs/utils.jl:95-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(t1::T, t2::T) where {T<:Union{HTML,Text}} = t1.content == t2.content
hash(t::T, h::UInt) where {T<:Union{HTML,Text}} = hash(T, hash(t.content, h))

```
-/
/- `t1 == t2` for `HTML`s or `Text`s of the same type `T`, whose contents are values: the contents'
`==`. -/
def eq_content {R : Type} (eq : X → X → R) (c1 c2 : X) : R := eq c1 c2

/-- `hash(t, h) = hash(T, hash(t.content, h))` for a value content, over `hash` of the type `T` and
of the content. -/
def hash_content (hashType : JInt .u64 → JInt .u64) (hashValue : X → JInt .u64 → JInt .u64) (c : X)
    (h : JInt .u64) : JInt .u64 :=
  hashType (hashValue c h)

end

/--
Julia source: base/docs/utils.jl:98-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @text_str -> Docs.Text

Create a `Text` object from a literal string.

# Examples
```jldoctest
julia> text"Julia"
Julia
```
"""
macro text_str(s)
    :(Text($s))
end

````
-/
/- `@text_str(s)` returns `:(Text($s))`. -/
def text_str {L : Type} (s : Value L) : Value L := .expr "call" [.symbol "Text", s]

section
variable {m : Type → Type} [Monad m] {Io X : Type}

/--
Julia source: base/docs/utils.jl:113-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function catdoc(xs::Text...)
    Text() do io
        for x in xs
            show(io, MIME"text/plain"(), x)
        end
    end
end
```
-/
/- `catdoc(xs::Text...)`. `show(io, MIME"text/plain"(), x)` of a `Text` is the
`base/multimedia.jl` fallback `show(io, x)`, which no method of this file specializes. -/
def catdoc_Text {Y : Type} (print : Io → X → m Unit) (xs : List (Text m Io X)) : Text m Io Y :=
  ⟨.func fun io => do
    for x in xs do
      show_Text print io x⟩

end

end JuliaLean.base.docs.utils
