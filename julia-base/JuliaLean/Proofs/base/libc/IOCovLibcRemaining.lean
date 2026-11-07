import JuliaLean.base.libc
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.io.IOCovCommon


section
namespace JuliaLean.IOCov.LibcRemaining

open JuliaLean.Registry

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
end
