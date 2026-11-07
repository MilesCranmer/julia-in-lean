import JuliaLean.base.io

/-!
# Model of `base/osinfo.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
OS symbols are their complete interned names. The `jl_get_UNAME` runtime call is
a typed primitive; unknown OS names retain the source's ArgumentError. Generated
zero-argument methods cache the build-time result, rather than querying the host.
WSL detection uses runtime filesystem queries with source short-circuit order.
-/

namespace JuliaLean.base.osinfo
open JuliaLean
open JuliaLean.base.io (M)

/--
Julia source: base/osinfo.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const KERNEL = ccall(:jl_get_UNAME, Any, ())::Symbol
```
-/
def kernel {World : Type} (jlGetUname : M World String) : M World String := jlGetUname

/--
Julia source: base/osinfo.jl:51-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islinux(os::Symbol) = (os === :Linux)
```
-/
def islinux (os : String) : Bool := os == "Linux"

/--
Julia source: base/osinfo.jl:78-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfreebsd(os::Symbol) = (os === :FreeBSD)
```
-/
def isfreebsd (os : String) : Bool := os == "FreeBSD"

/--
Julia source: base/osinfo.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isopenbsd(os::Symbol) = (os === :OpenBSD)
```
-/
def isopenbsd (os : String) : Bool := os == "OpenBSD"

/--
Julia source: base/osinfo.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnetbsd(os::Symbol) = (os === :NetBSD)
```
-/
def isnetbsd (os : String) : Bool := os == "NetBSD"

/--
Julia source: base/osinfo.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdragonfly(os::Symbol) = (os === :DragonFly)
```
-/
def isdragonfly (os : String) : Bool := os == "DragonFly"

/--
Julia source: base/osinfo.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iswindows(os::Symbol) = (os === :Windows || os === :NT)
```
-/
def iswindows (os : String) : Bool := os == "Windows" || os == "NT"

/--
Julia source: base/osinfo.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isapple(os::Symbol) = (os === :Apple || os === :Darwin)
```
-/
def isapple (os : String) : Bool := os == "Apple" || os == "Darwin"

/--
Julia source: base/osinfo.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isjsvm(os::Symbol) = (os === :Emscripten)
```
-/
def isjsvm (os : String) : Bool := os == "Emscripten"

/--
Julia source: base/osinfo.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isbsd(os::Symbol) = (isfreebsd(os) || isopenbsd(os) || isnetbsd(os) || isdragonfly(os) || isapple(os))
```
-/
def isbsd (os : String) : Bool :=
  isfreebsd os || isopenbsd os || isnetbsd os || isdragonfly os || isapple os

/--
Julia source: base/osinfo.jl:29-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isunix(os::Symbol)
    if iswindows(os)
        return false
    elseif islinux(os) || isbsd(os)
        return true
    elseif os === :Emscripten
        # Emscripten implements the POSIX ABI and provides traditional
        # Unix-style operating system functions such as file system support.
        # Therefore, we consider it a unix, even though this need not be
        # generally true for a jsvm embedding.
        return true
    else
        throw(ArgumentError("unknown operating system \"$os\""))
    end
end
```
-/
def isunix (os : String) : Jl Bool := do
  if iswindows os then pure false
  else if islinux os || isbsd os then pure true
  else if os == "Emscripten" then pure true
  else throw (.argumentError ("unknown operating system \"" ++ os ++ "\""))

/--
Julia source: base/osinfo.jl:162-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function detectwsl()
    # We use the same approach as canonical/snapd do to detect WSL
    islinux() && (
        isfile("/proc/sys/fs/binfmt_misc/WSLInterop")
        || isdir("/run/WSL")
    )
end
```
-/
def detectwsl {World : Type} (islinux : Bool)
    (isfile isdir : String → M World Bool) : M World Bool := do
  if !islinux then return false
  if ← isfile "/proc/sys/fs/binfmt_misc/WSLInterop" then return true
  isdir "/run/WSL"

structure CachedPredicates where
  isunix : Bool
  islinux : Bool
  isbsd : Bool
  isapple : Bool
  iswindows : Bool
  isfreebsd : Bool
  isopenbsd : Bool
  isnetbsd : Bool
  isdragonfly : Bool
  isjsvm : Bool

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def buildPredicates (kernel : String) : Jl CachedPredicates := do
  let unix ← isunix kernel
  pure ⟨unix, islinux kernel, isbsd kernel, isapple kernel, iswindows kernel,
    isfreebsd kernel, isopenbsd kernel, isnetbsd kernel, isdragonfly kernel, isjsvm kernel⟩

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isunixDefault (built : CachedPredicates) : Bool := built.isunix

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def islinuxDefault (built : CachedPredicates) : Bool := built.islinux

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isbsdDefault (built : CachedPredicates) : Bool := built.isbsd

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isappleDefault (built : CachedPredicates) : Bool := built.isapple

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def iswindowsDefault (built : CachedPredicates) : Bool := built.iswindows

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isfreebsdDefault (built : CachedPredicates) : Bool := built.isfreebsd

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isopenbsdDefault (built : CachedPredicates) : Bool := built.isopenbsd

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isnetbsdDefault (built : CachedPredicates) : Bool := built.isnetbsd

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isdragonflyDefault (built : CachedPredicates) : Bool := built.isdragonfly

/--
Julia source: base/osinfo.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isunix, :islinux, :isbsd, :isapple, :iswindows, :isfreebsd, :isopenbsd, :isnetbsd, :isdragonfly, :isjsvm)
    @eval $f() = $(getfield(@__MODULE__, f)(KERNEL))
end
```
-/
def isjsvmDefault (built : CachedPredicates) : Bool := built.isjsvm


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/osinfo.jl:1-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # NB: This file is `Core.eval`-uated into the (pre-existing) module Sys
-- 
-- export KERNEL,
--        isapple,
--        isbsd,
--        isdragonfly,
--        isfreebsd,
--        islinux,
--        isnetbsd,
--        isopenbsd,
--        isunix,
--        iswindows,
--        isjsvm,
--        detectwsl
-- 
-- """
--     Sys.KERNEL::Symbol
-- 
-- A symbol representing the name of the operating system, as returned by `uname` of the build configuration.
-- """
-- /Source

-- Source: base/osinfo.jl:23-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Sys.isunix([os])
-- 
-- Predicate for testing if the OS provides a Unix-like interface.
-- See documentation in [Handling Operating System Variation](@ref).
-- """
-- /Source

-- Source: base/osinfo.jl:44-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.islinux([os])
-- 
-- Predicate for testing if the OS is a derivative of Linux.
-- See documentation in [Handling Operating System Variation](@ref).
-- """
-- /Source

-- Source: base/osinfo.jl:52-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.isbsd([os])
-- 
-- Predicate for testing if the OS is a derivative of BSD.
-- See documentation in [Handling Operating System Variation](@ref).
-- 
-- !!! note
--     The Darwin kernel descends from BSD, which means that `Sys.isbsd()` is
--     `true` on macOS systems. To exclude macOS from a predicate, use
--     `Sys.isbsd() && !Sys.isapple()`.
-- """
-- /Source

-- Source: base/osinfo.jl:65-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.isfreebsd([os])
-- 
-- Predicate for testing if the OS is a derivative of FreeBSD.
-- See documentation in [Handling Operating System Variation](@ref).
-- 
-- !!! note
--     Not to be confused with `Sys.isbsd()`, which is `true` on FreeBSD but also on
--     other BSD-based systems. `Sys.isfreebsd()` refers only to FreeBSD.
-- !!! compat "Julia 1.1"
--     This function requires at least Julia 1.1.
-- """
-- /Source

-- Source: base/osinfo.jl:79-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.isopenbsd([os])
-- 
-- Predicate for testing if the OS is a derivative of OpenBSD.
-- See documentation in [Handling Operating System Variation](@ref).
-- 
-- !!! note
--     Not to be confused with `Sys.isbsd()`, which is `true` on OpenBSD but also on
--     other BSD-based systems. `Sys.isopenbsd()` refers only to OpenBSD.
-- !!! compat "Julia 1.1"
--     This function requires at least Julia 1.1.
-- """
-- /Source

-- Source: base/osinfo.jl:93-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.isnetbsd([os])
-- 
-- Predicate for testing if the OS is a derivative of NetBSD.
-- See documentation in [Handling Operating System Variation](@ref).
-- 
-- !!! note
--     Not to be confused with `Sys.isbsd()`, which is `true` on NetBSD but also on
--     other BSD-based systems. `Sys.isnetbsd()` refers only to NetBSD.
-- !!! compat "Julia 1.1"
--     This function requires at least Julia 1.1.
-- """
-- /Source

-- Source: base/osinfo.jl:107-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.isdragonfly([os])
-- 
-- Predicate for testing if the OS is a derivative of DragonFly BSD.
-- See documentation in [Handling Operating System Variation](@ref).
-- 
-- !!! note
--     Not to be confused with `Sys.isbsd()`, which is `true` on DragonFly but also on
--     other BSD-based systems. `Sys.isdragonfly()` refers only to DragonFly.
-- !!! compat "Julia 1.1"
--     This function requires at least Julia 1.1.
-- """
-- /Source

-- Source: base/osinfo.jl:121-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.iswindows([os])
-- 
-- Predicate for testing if the OS is a derivative of Microsoft Windows NT.
-- See documentation in [Handling Operating System Variation](@ref).
-- """
-- /Source

-- Source: base/osinfo.jl:129-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.isapple([os])
-- 
-- Predicate for testing if the OS is a derivative of Apple Macintosh OS X or Darwin.
-- See documentation in [Handling Operating System Variation](@ref).
-- """
-- /Source

-- Source: base/osinfo.jl:137-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.isjsvm([os])
-- 
-- Predicate for testing if Julia is running in a JavaScript VM (JSVM),
-- including e.g. a WebAssembly JavaScript embedding in a web browser.
-- 
-- !!! compat "Julia 1.2"
--     This function requires at least Julia 1.2.
-- """
-- /Source

-- Source: base/osinfo.jl:148-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.detectwsl()
-- 
-- Runtime predicate for testing if Julia is running inside
-- Windows Subsystem for Linux (WSL).
-- 
-- !!! note
--     Unlike `Sys.iswindows`, `Sys.islinux` etc., this is a runtime test, and thus
--     cannot meaningfully be used in `@static if` constructs.
-- 
-- !!! compat "Julia 1.12"
--     This function requires at least Julia 1.12.
-- """
-- /Source

-- Source: base/osinfo.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


end JuliaLean.base.osinfo
