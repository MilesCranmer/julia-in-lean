import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.uuid

/-!
# Model of `base/pkgid.jl`

Typed model of `Base.PkgId` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. `name` is the bytes
of a `String`; constructors taking an `AbstractString` convert it with a given `String(name)`.
`UUID` is the `base/uuid.jl` model. Module reflection (`jl_module_uuid`, `nameof(moduleroot(m))`),
generic `hash` dispatch, printing and the `IOBuffer` reads and writes of `binpack`/`binunpack` are
parameters.
-/

namespace JuliaLean.base.pkgid

open JuliaLean
open JuliaLean.base.uuid (UUID U64 U128)

abbrev Bytes := List UInt8

-- UNTRANSLATED
-- license header; no method
-- Source: base/pkgid.jl:1-2 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- /Source

/--
Julia source: base/pkgid.jl:3-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PkgId
    uuid::Union{UUID,Nothing}
    name::String

    PkgId(u::UUID, name::AbstractString) = new(UInt128(u) == 0 ? nothing : u, name)
    PkgId(::Nothing, name::AbstractString) = new(nothing, name)
end
```
-/
structure PkgId where
  uuid : Option UUID
  name : Bytes
  deriving DecidableEq, Repr

def PkgId_UUID {A : Type} (toString : A → Bytes) (u : UUID) (name : A) : PkgId :=
  ⟨if (JuliaLean.base.uuid.toUInt128 u).val == 0 then none else some u, toString name⟩
def PkgId_Nothing {A : Type} (toString : A → Bytes) (name : A) : PkgId :=
  ⟨none, toString name⟩

/--
Julia source: base/pkgid.jl:10-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PkgId(name::AbstractString) = PkgId(nothing, name)

```
-/
def PkgId_1 {A : Type} (toString : A → Bytes) (name : A) : PkgId :=
  PkgId_Nothing toString name

/--
Julia source: base/pkgid.jl:12-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PkgId(m::Module, name::String = String(nameof(moduleroot(m))))
    uuid = UUID(ccall(:jl_module_uuid, NTuple{2, UInt64}, (Any,), m))
    UInt128(uuid) == 0 ? PkgId(name) : PkgId(uuid, name)
end

```
-/
-- `jl_module_uuid` and `String(nameof(moduleroot(m)))` (the default `name`) are runtime
-- reflection on the module `m`.
def PkgId_Module {Mod : Type} (jl_module_uuid : Mod → U64 × U64) (nameof_moduleroot : Mod → Bytes)
    (m : Mod) (name : Option Bytes := none) : PkgId :=
  let name := name.getD (nameof_moduleroot m)
  let uuid := JuliaLean.base.uuid.uuidFromTuple2 (jl_module_uuid m)
  if (JuliaLean.base.uuid.toUInt128 uuid).val == 0 then PkgId_1 id name else PkgId_UUID id uuid name

/--
Julia source: base/pkgid.jl:17-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::PkgId, b::PkgId) = a.uuid == b.uuid && a.name == b.name

```
-/
-- `a.uuid == b.uuid` on `Union{UUID,Nothing}`: `nothing == nothing`, a `UUID` and `nothing` differ,
-- and two `UUID`s compare their `value`s (`==` falls back to `===` on the immutable struct).
def eq (a b : PkgId) : Bool := a.uuid == b.uuid && a.name == b.name

/--
Julia source: base/pkgid.jl:19-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(pkg::PkgId, h::UInt)
    h ⊻= 0xc9f248583a0ca36c % UInt
    h = hash(pkg.uuid, h)
    h = hash(pkg.name, h)
    return h
end

```
-/
-- `hash(::Nothing, h)` and `hash(::String, h)` are given; `hash(::UUID, h)` is `base/uuid.jl`'s.
def hash (hashAny : {T : Type} → T → U64 → U64) (hash_nothing : U64 → U64) (hash_string : Bytes → U64 → U64)
    (pkg : PkgId) (h : U64) : U64 :=
  let h := JuliaLean.base.int.bxor h (JInt.lit .u64 0xc9f248583a0ca36c)
  let h := match pkg.uuid with
    | none => hash_nothing h
    | some u => JuliaLean.base.uuid.hashUUID hashAny u h
  let h := hash_string pkg.name h
  h

/-- An argument of `print(io, xs...)`. -/
inductive PrintArg where
  | str (s : Bytes)
  | uuid (u : UUID)

/--
Julia source: base/pkgid.jl:26-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO,  ::MIME"text/plain", pkg::PkgId) =
    print(io, pkg.name, " [", pkg.uuid === nothing ? "top-level" : pkg.uuid, "]")

```
-/
-- `print(io, xs...)` is given as `print` on the list of arguments.
def show_textplain {m : Type → Type} {IO : Type} (print : IO → List PrintArg → m Unit) (io : IO) (pkg : PkgId) :
    m Unit :=
  print io [.str pkg.name, .str " [".toUTF8.toList,
    (match pkg.uuid with
      | none => .str "top-level".toUTF8.toList
      | some u => .uuid u),
    .str "]".toUTF8.toList]

/-- `IOBuffer` operations (`base/iobuffer.jl`, `base/io.jl`) used by `binpack` and `binunpack`. -/
structure BufOps (m : Type → Type) (Buf : Type) where
  /-- `IOBuffer()` and `IOBuffer(s)`. -/
  new : m Buf
  ofString : Bytes → m Buf
  write_UInt8 : Buf → UInt8 → m Unit
  write_UInt128 : Buf → U128 → m Unit
  write_String : Buf → Bytes → m Unit
  unsafe_takestring : Buf → m Bytes
  read_UInt8 : Buf → m UInt8
  read_UInt128 : Buf → m U128
  read_String : Buf → m Bytes
  /-- `@assert cond msg` failing: an `AssertionError`. -/
  assertionError : {α : Type} → String → m α

/--
Julia source: base/pkgid.jl:29-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function binpack(pkg::PkgId)
    io = IOBuffer()
    write(io, UInt8(0))
    uuid = pkg.uuid
    write(io, uuid === nothing ? UInt128(0) : UInt128(uuid))
    write(io, pkg.name)
    return unsafe_takestring!(io)
end

```
-/
def binpack {m : Type → Type} [Monad m] {Buf : Type} (b : BufOps m Buf) (pkg : PkgId) : m Bytes := do
  let io ← b.new
  b.write_UInt8 io 0
  let uuid := pkg.uuid
  b.write_UInt128 io (match uuid with
    | none => JInt.lit .u128 0
    | some u => JuliaLean.base.uuid.toUInt128 u)
  b.write_String io pkg.name
  b.unsafe_takestring io

/--
Julia source: base/pkgid.jl:38-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function binunpack(s::String)
    io = IOBuffer(s)
    z = read(io, UInt8)
    @assert z === 0x00 "unexpected data"
    uuid = read(io, UInt128)
    name = read(io, String)
    return PkgId(UUID(uuid), name)
end
```
-/
def binunpack {m : Type → Type} [Monad m] {Buf : Type} (b : BufOps m Buf) (s : Bytes) : m PkgId := do
  let io ← b.ofString s
  let z ← b.read_UInt8 io
  if !(z == 0x00) then b.assertionError "unexpected data"
  let uuid ← b.read_UInt128 io
  let name ← b.read_String io
  return PkgId_UUID id ⟨uuid⟩ name

end JuliaLean.base.pkgid

namespace JuliaLean.IntFuncsCov.UuidPkgid

open JuliaLean
open JuliaLean.Base64Uuid
open JuliaLean.ParsePrint


structure PkgId where
  uuid : Option UUID
  name : List UInt8
  deriving DecidableEq

def pkgId (u : UUID) (name : List UInt8) : PkgId :=
  ⟨if u.value.val = 0 then none else some u, name⟩

def pkgIdNothing (name : List UInt8) : PkgId := ⟨none, name⟩

def pkgHash (hashUuid : Option UUID → UInt64 → UInt64)
    (hashName : List UInt8 → UInt64 → UInt64) (p : PkgId) (h : UInt64) : UInt64 :=
  let h := h ^^^ 0xc9f248583a0ca36c
  hashName p.name (hashUuid p.uuid h)

structure PackedPkgId where
  tag : UInt8
  uuid : JInt .u128
  name : List UInt8
  deriving DecidableEq

def binpack (p : PkgId) : PackedPkgId :=
  ⟨0, p.uuid.map (·.value) |>.getD (JInt.lit .u128 0), p.name⟩

def binunpack (p : PackedPkgId) : Jl PkgId :=
  if p.tag = 0 then .ok (pkgId ⟨p.uuid⟩ p.name)
  else .error (.argumentError "unexpected data")

end JuliaLean.IntFuncsCov.UuidPkgid
