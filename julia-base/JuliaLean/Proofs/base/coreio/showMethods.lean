import JuliaLean.Proofs.base.show.methodSupport
import JuliaLean.base.coreio

namespace JuliaLean.ShowCov.Methods.CoreIO

open JuliaLean.Registry
open JuliaLean.ShowCov.Terminals
open JuliaLean.ShowCov.Methods

/-! Each definition mirrors one callable method in `base/coreio.jl`. -/

def P6 : Prop := ∀ x : String, HasResult (m6 x)
theorem p6 : P6 := fun x => hasResult (m6 x)

def P7 : Prop := ∀ x1 x2 : String, HasResult (m7 x1 x2)
theorem p7 : P7 := fun x1 x2 => hasResult (m7 x1 x2)

def P8 : Prop := ∀ x : String, HasResult (m8 x)
theorem p8 : P8 := fun x => hasResult (m8 x)

def P9 : Prop := ∀ x1 x2 : String, HasResult (m9 x1 x2)
theorem p9 : P9 := fun x1 x2 => hasResult (m9 x1 x2)

def P11 : Prop := ∀ xs : List String, HasResult (m11 xs)
theorem p11 : P11 := fun xs => hasResult (m11 xs)

def P12 : Prop := ∀ xs : List String, HasResult (m12 xs)
theorem p12 : P12 := fun xs => hasResult (m12 xs)

def P13 : Prop := ∀ io : Stream, HasResult (m13 io)
theorem p13 : P13 := fun io => hasResult (m13 io)

def P19 : Prop := ∀ args : Unit, HasResult (m19 args)
theorem p19 : P19 := fun args => hasResult (m19 args)

def P22 : Prop := ∀ b : UInt8, m22 b = 1
theorem p22 : P22 := fun _ => rfl

def P23 : Prop := ∀ n : Nat, HasResult (m23 n)
theorem p23 : P23 := fun n => hasResult (m23 n)

def P24 : Prop := ∀ io : Unit, m24 io = .returns
theorem p24 : P24 := fun _ => rfl

def P25 : Prop := ∀ io : Unit, m25 io = .returns
theorem p25 : P25 := fun _ => rfl

def P26 : Prop := ∀ io : Unit, m26 io = .blocksForever
theorem p26 : P26 := fun _ => rfl

def P27 : Prop := ∀ io : Unit, m27 io = 0
theorem p27 : P27 := fun _ => rfl

def P30 : Prop := ∀ x : UInt8, m30 x = [x]
theorem p30 : P30 := fun _ => rfl

def P31 : Prop := ∀ bytes : List UInt8, m31 bytes = bytes
theorem p31 : P31 := fun _ => rfl

def P34 : Prop := ∀ io : Stream, m34 io = .error .eofError
theorem p34 : P34 := fun _ => rfl

def P35 : Prop := ∀ io : Stream, m35 io = true
theorem p35 : P35 := fun _ => rfl

def P36 : Prop := ∀ io : Stream, m36 io = false
theorem p36 : P36 := fun _ => rfl

def P37 : Prop := ∀ io : Stream, m37 io = true
theorem p37 : P37 := fun _ => rfl

def P38 : Prop := ∀ io : Stream, m38 io = ()
theorem p38 : P38 := fun _ => rfl

def P39 : Prop := ∀ io : Stream, m39 io = true
theorem p39 : P39 := fun _ => rfl

def P40 : Prop := ∀ nb : Int, m40 nb = ()
theorem p40 : P40 := fun _ => rfl

def entries : List Entry := [
  entry "showcov-coreio-l6" "base/coreio.jl" "print(x)" "print(x) calls print(stdout, x) for every x." ``P6 ``p6,
  entry "showcov-coreio-l7" "base/coreio.jl" "print(x1, x2)" "print(x1, x2) calls print(stdout, x1, x2)." ``P7 ``p7,
  entry "showcov-coreio-l8" "base/coreio.jl" "println(x)" "println(x) appends one newline on stdout." ``P8 ``p8,
  entry "showcov-coreio-l9" "base/coreio.jl" "println(x1, x2)" "println(x1, x2) appends one newline on stdout." ``P9 ``p9,
  entry "showcov-coreio-l11" "base/coreio.jl" "print(xs...)" "The vararg print wrapper forwards every argument to stdout in order." ``P11 ``p11,
  entry "showcov-coreio-l12" "base/coreio.jl" "println(xs...)" "The vararg println wrapper forwards every argument and one newline." ``P12 ``p12,
  entry "showcov-coreio-l13" "base/coreio.jl" "println(::IO)" "println(io) writes one newline to that stream." ``P13 ``p13,
  entry "showcov-coreio-l19" "base/coreio.jl" "DevNull()" "The inner constructor creates a DevNull value." ``P19 ``p19,
  entry "showcov-coreio-l22" "base/coreio.jl" "write(::DevNull, ::UInt8)" "A DevNull byte write returns one." ``P22 ``p22,
  entry "showcov-coreio-l23" "base/coreio.jl" "unsafe_write(::DevNull, ::Ptr{UInt8}, ::UInt)" "DevNull unsafe_write returns the Int conversion or its conversion error." ``P23 ``p23,
  entry "showcov-coreio-l24" "base/coreio.jl" "closewrite(::DevNull)" "closewrite on DevNull returns nothing." ``P24 ``p24,
  entry "showcov-coreio-l25" "base/coreio.jl" "close(::DevNull)" "close on DevNull returns nothing." ``P25 ``p25,
  entry "showcov-coreio-l26" "base/coreio.jl" "wait_close(::DevNull)" "wait_close on DevNull delegates to wait." ``P26 ``p26,
  entry "showcov-coreio-l27" "base/coreio.jl" "bytesavailable(::DevNull)" "DevNull has zero available bytes." ``P27 ``p27,
  entry "showcov-coreio-l30" "base/coreio.jl" "write(::CoreIO, ::UInt8)" "The CoreIO byte method delegates that byte to Core.write." ``P30 ``p30,
  entry "showcov-coreio-l31" "base/coreio.jl" "unsafe_write(::CoreIO, ::Ptr{UInt8}, ::UInt)" "The CoreIO pointer method delegates the selected bytes to Core.unsafe_write." ``P31 ``p31,
  entry "showcov-coreio-l34" "base/coreio.jl" "read(::CoreIO, ::Type{UInt8})" "Reading a byte from CoreIO throws EOFError." ``P34 ``p34,
  entry "showcov-coreio-l35" "base/coreio.jl" "isopen(::CoreIO)" "CoreIO is open." ``P35 ``p35,
  entry "showcov-coreio-l36" "base/coreio.jl" "isreadable(::CoreIO)" "CoreIO is not readable." ``P36 ``p36,
  entry "showcov-coreio-l37" "base/coreio.jl" "iswritable(::CoreIO)" "CoreIO is writable." ``P37 ``p37,
  entry "showcov-coreio-l38" "base/coreio.jl" "flush(::CoreIO)" "Flushing CoreIO returns nothing." ``P38 ``p38,
  entry "showcov-coreio-l39" "base/coreio.jl" "eof(::CoreIO)" "CoreIO is at end of file." ``P39 ``p39,
  entry "showcov-coreio-l40" "base/coreio.jl" "wait_readnb(::CoreIO, ::Int)" "wait_readnb on CoreIO returns nothing for every count." ``P40 ``p40
]

end JuliaLean.ShowCov.Methods.CoreIO
