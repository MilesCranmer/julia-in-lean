import JuliaLean.Core
import JuliaLean.Runtime.Float

/-!
# Model of `base/ctypes.jl`

C integer aliases use `JInt` at Julia's fixed widths, and the floating aliases use the IEEE
binary32 and binary64 value models.
-/

namespace JuliaLean.base.ctypes

open JuliaLean JuliaLean.Promotion

/--
Julia source: base/ctypes.jl:6-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cuchar

Equivalent to the native `unsigned char` c-type ([`UInt8`](@ref)).
"""
const Cuchar = UInt8
```
-/
abbrev Cuchar := JInt .u8

/--
Julia source: base/ctypes.jl:14-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cshort

Equivalent to the native `signed short` c-type ([`Int16`](@ref)).
"""
const Cshort = Int16
```
-/
abbrev Cshort := JInt .i16

/--
Julia source: base/ctypes.jl:22-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cushort

Equivalent to the native `unsigned short` c-type ([`UInt16`](@ref)).
"""
const Cushort = UInt16
```
-/
abbrev Cushort := JInt .u16

/--
Julia source: base/ctypes.jl:30-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cint

Equivalent to the native `signed int` c-type ([`Int32`](@ref)).
"""
const Cint = Int32
```
-/
abbrev Cint := JInt .i32

/--
Julia source: base/ctypes.jl:38-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cuint

Equivalent to the native `unsigned int` c-type ([`UInt32`](@ref)).
"""
const Cuint = UInt32
```
-/
abbrev Cuint := JInt .u32

/--
Julia source: base/ctypes.jl:46-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cptrdiff_t

Equivalent to the native `ptrdiff_t` c-type (`Int`).
"""
const Cptrdiff_t = Int
```
-/
abbrev Cptrdiff_t := JInt .i64

/--
Julia source: base/ctypes.jl:54-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Csize_t

Equivalent to the native `size_t` c-type (`UInt`).
"""
const Csize_t = UInt
```
-/
abbrev Csize_t := JInt .u64

/--
Julia source: base/ctypes.jl:62-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cssize_t

Equivalent to the native `ssize_t` c-type.
"""
const Cssize_t = Int
```
-/
abbrev Cssize_t := JInt .i64

/--
Julia source: base/ctypes.jl:70-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cintmax_t

Equivalent to the native `intmax_t` c-type ([`Int64`](@ref)).
"""
const Cintmax_t = Int64
```
-/
abbrev Cintmax_t := JInt .i64

/--
Julia source: base/ctypes.jl:78-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cuintmax_t

Equivalent to the native `uintmax_t` c-type ([`UInt64`](@ref)).
"""
const Cuintmax_t = UInt64
```
-/
abbrev Cuintmax_t := JInt .u64

/--
Julia source: base/ctypes.jl:86-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Clonglong

Equivalent to the native `signed long long` c-type ([`Int64`](@ref)).
"""
const Clonglong = Int64
```
-/
abbrev Clonglong := JInt .i64

/--
Julia source: base/ctypes.jl:94-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Culonglong

Equivalent to the native `unsigned long long` c-type ([`UInt64`](@ref)).
"""
const Culonglong = UInt64
```
-/
abbrev Culonglong := JInt .u64

/--
Julia source: base/ctypes.jl:102-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cfloat

Equivalent to the native `float` c-type ([`Float32`](@ref)).
"""
const Cfloat = Float32
```
-/
abbrev Cfloat := Fl single

/--
Julia source: base/ctypes.jl:110-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Cdouble

Equivalent to the native `double` c-type ([`Float64`](@ref)).
"""
const Cdouble = Float64
```
-/
abbrev Cdouble := Fl double

end JuliaLean.base.ctypes
