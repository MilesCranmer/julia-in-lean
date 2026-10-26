import JuliaLean.Registry.Types

namespace JuliaLean.IOCov.LibcRemaining

open JuliaLean.Registry

/-- Unix `_get_osfhandle(fd::RawFD)`, `base/libc.jl:86`. -/
def getOsfhandle (fd : Int) : Int := fd

/-- `_make_uint64_seed()`, `base/libc.jl:462`.  `getrandom` models filling the
fresh `RefValue{UInt64}` before it is indexed. -/
def makeUint64Seed (getrandom : UInt64 -> UInt64) : UInt64 := getrandom 0

def GetOsfhandleIdentity : Prop := forall fd, getOsfhandle fd = fd
theorem getOsfhandleIdentity : GetOsfhandleIdentity := by intro; rfl

def MakeSeedReturnsFilledRef : Prop := forall getrandom,
  makeUint64Seed getrandom = getrandom 0
theorem makeSeedReturnsFilledRef : MakeSeedReturnsFilledRef := by intro; rfl

def entries : List Entry := [
  { id := "iocov-libc-get-osfhandle", juliaFile := "base/libc.jl",
    juliaFns := ["_get_osfhandle(::RawFD)"],
    statement := "On Unix, _get_osfhandle returns the file descriptor unchanged.",
    source := "base/libc.jl:86", status := .proven,
    prop := ``GetOsfhandleIdentity, thm := some ``getOsfhandleIdentity },
  { id := "iocov-libc-make-seed", juliaFile := "base/libc.jl",
    juliaFns := ["_make_uint64_seed()"],
    statement := "The seed helper returns the UInt64 written by getrandom! into a fresh reference.",
    source := "base/libc.jl:462", status := .proven,
    prop := ``MakeSeedReturnsFilledRef, thm := some ``makeSeedReturnsFilledRef }
]

end JuliaLean.IOCov.LibcRemaining
