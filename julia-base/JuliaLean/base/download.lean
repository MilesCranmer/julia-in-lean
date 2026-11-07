import JuliaLean.Core

/-!
# Model of `base/download.jl`

Typed wrappers for the deprecated download API at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Package loading, deprecation warnings, and the
latest-world `Downloads.download` call are explicit callbacks.
-/

namespace JuliaLean.base.download

open JuliaLean

-- UNTRANSLATED
-- Source: base/download.jl:1-1 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- /Source
-- Reason: The file license header has no executable behavior.
/--
Julia source: base/download.jl:3-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Downloads() = require(PkgId(
        UUID((0xf43a241f_c20a_4ad4, 0x852c_f6b1247861c6)),
        "Downloads",
    ))
```
-/
structure DownloadOps (m : Type → Type)
    (PackageId DownloadsModule URL Path Symbol : Type) where
  packageId : JInt .u64 → JInt .u64 → String → PackageId
  require : PackageId → m DownloadsModule
  deprecationWarning : String → Symbol → m Unit
  downloadSymbol : Symbol
  invokelatestDownload : DownloadsModule → URL → Option Path → m Path

def downloads {m : Type → Type} {PackageId DownloadsModule : Type}
    [Monad m] (packageId : JInt .u64 → JInt .u64 → String → PackageId)
    (require : PackageId → m DownloadsModule) : m DownloadsModule :=
  require (packageId (JInt.lit .u64 0xf43a241fc20a4ad4)
    (JInt.lit .u64 0x852cf6b1247861c6) "Downloads")

/--
Julia source: base/download.jl:8-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    download(url::AbstractString, [path::AbstractString = tempname()]) -> path

Download a file from the given url, saving it to the location `path`, or if not
specified, a temporary path. Returns the path of the downloaded file.

!!! note
    Since Julia 1.6, this function is deprecated and is just a thin wrapper
    around `Downloads.download`. In new code, you should use that function
    directly instead of calling this.
"""
download(url::AbstractString, path::AbstractString) = do_download(url, path)
```
-/
def downloadToPath {m : Type → Type} {URL Path : Type} [Monad m]
    (doDownload : URL → Option Path → m Path) (url : URL) (path : Path) : m Path :=
  doDownload url (some path)

/--
Julia source: base/download.jl:8-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    download(url::AbstractString, [path::AbstractString = tempname()]) -> path

Download a file from the given url, saving it to the location `path`, or if not
specified, a temporary path. Returns the path of the downloaded file.

!!! note
    Since Julia 1.6, this function is deprecated and is just a thin wrapper
    around `Downloads.download`. In new code, you should use that function
    directly instead of calling this.
"""
```
Julia source: base/download.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
download(url::AbstractString) = do_download(url, nothing)
```
-/
def downloadToTemp {m : Type → Type} {URL Path : Type} [Monad m]
    (doDownload : URL → Option Path → m Path) (url : URL) : m Path :=
  doDownload url none

/--
Julia source: base/download.jl:22-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function do_download(url::AbstractString, path::Union{AbstractString, Nothing})
    depwarn("Base.download is deprecated; use Downloads.download instead", :download)
    invokelatest(Downloads().download, url, path)
end
```
-/
def doDownload {m : Type → Type} {PackageId DownloadsModule URL Path Symbol : Type} [Monad m]
    (ops : DownloadOps m PackageId DownloadsModule URL Path Symbol)
    (url : URL) (path : Option Path) : m Path := do
  ops.deprecationWarning "Base.download is deprecated; use Downloads.download instead" ops.downloadSymbol
  let module ← downloads ops.packageId ops.require
  ops.invokelatestDownload module url path

end JuliaLean.base.download

namespace JuliaLean.MiscCov.BaseJl

/-! ## `base/download.jl` -/

/-- `Downloads()`: `require(PkgId(UUID((0xf43a241f_c20a_4ad4, 0x852c_f6b1247861c6)),
"Downloads"))`, `base/download.jl:3-6`; the UUID is the 128-bit number with the
first tuple element as its high half. -/
def downloadsUuid : Nat := 0xf43a241f_c20a_4ad4 * 2 ^ 64 + 0x852c_f6b1247861c6

/-- The effects of `do_download(url, path)`, `base/download.jl:22-25`: the
deprecation warning, loading `Downloads`, then `Downloads.download(url, path)`;
`path = none` is `nothing`. -/
inductive DlEv where
  | depwarn (msg : String) (funcsym : String)
  | require (uuid : Nat) (name : String)
  | download (url : String) (path : Option String)
  deriving DecidableEq, Repr

def doDownload (url : String) (path : Option String) : List DlEv :=
  [.depwarn "Base.download is deprecated; use Downloads.download instead" "download",
   .require downloadsUuid "Downloads", .download url path]

/-- `download(url, path)` and `download(url)`, `base/download.jl:19-20`. -/
def download2 (url path : String) : List DlEv := doDownload url (some path)
def download1 (url : String) : List DlEv := doDownload url none

end JuliaLean.MiscCov.BaseJl
