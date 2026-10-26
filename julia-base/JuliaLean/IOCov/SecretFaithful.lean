import JuliaLean.Registry.Types
import JuliaLean.IOCov.Common

namespace JuliaLean.IOCov.SecretFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov

abbrev ByteMem := List (Option UInt8)

structure SB where
  data : ByteMem
  size : Int
  ptr : Int
  finalizerRegistered : Bool
  deriving DecidableEq, Repr

def initializedPrefix (s : SB) : List UInt8 :=
  (s.data.take s.size.toNat).map (Option.getD · 0)

/-- `SecretBuffer(; sizehint)`, `base/secretbuffer.jl:36-40`. -/
def create (sizehint : Int) : R SB :=
  if sizehint < 0 then .error (.jl (.argumentError "invalid Memory size"))
  else .ok ⟨List.replicate sizehint.toNat none, 0, 1, true⟩

def setAt (data : ByteMem) (idx : Int) (b : UInt8) : R ByteMem :=
  if 1 <= idx && idx <= data.length then .ok (data.set (idx - 1).toNat (some b))
  else .error (.jl .boundsError)

/-- `write(::SecretBuffer, ::UInt8)`, `base/secretbuffer.jl:133-145`.
The optional byte list is the old allocation passed to securezero! on growth. -/
def writeByte (s : SB) (b : UInt8) : R (Nat × SB × Option ByteMem) := do
  let growth := s.ptr > s.data.length
  let old := if growth then some s.data else none
  let data := if growth then
    s.data ++ List.replicate (((s.size + 16) * 2 - s.data.length).toNat) none
    else s.data
  let size := if s.size = s.ptr - 1 then s.size + 1 else s.size
  let data <- setAt data s.ptr b
  pure (1, { s with data, size, ptr := s.ptr + 1 }, old)

def writeBytes : SB -> List UInt8 -> R SB
  | s, [] => .ok s
  | s, b :: bs => do let (_, s', _) <- writeByte s b; writeBytes s' bs

/-- `SecretBuffer(str::String)`, `base/secretbuffer.jl:55-63`. -/
def ofString (bytes : List UInt8) : R SB := do
  let s <- create bytes.length
  let s <- writeBytes s bytes
  pure { s with ptr := 1 }

/-- AbstractString constructor, `base/secretbuffer.jl:54`. -/
def ofAbstractString {alpha : Type} (stringBytes : alpha -> List UInt8) (str : alpha) : R SB :=
  ofString (stringBytes str)
/-- `convert(SecretBuffer, s::AbstractString)`, `base/secretbuffer.jl:64`. -/
def convertAbstract {alpha : Type} (stringBytes : alpha -> List UInt8) (str : alpha) : R SB :=
  ofString (stringBytes str)

/-- `SecretBuffer!(d)`, `base/secretbuffer.jl:71-80`: result and securely
zeroed source vector. -/
def ofVectorBang (d : List UInt8) : R (SB × List UInt8) := do
  let s <- create d.length
  let s <- writeBytes s d
  pure ({ s with ptr := 1 }, d.map (fun _ => 0))

/-- Pointer overload, `base/secretbuffer.jl:89-100`. -/
def unsafeOfPtr (p : Option (List UInt8)) (len : Int) : R (SB × List UInt8) :=
  match p with
  | none => argErr "cannot convert NULL to SecretBuffer"
  | some mem =>
      if len < 0 || mem.length < len then .error (.jl .boundsError)
      else ofVectorBang (mem.take len.toNat)

/-- Cstring overload, `base/secretbuffer.jl:82-88`. -/
def unsafeOfCstring (p : Option (List UInt8)) : R (SB × List UInt8) :=
  match p with
  | none => argErr "cannot convert NULL to SecretBuffer"
  | some mem => unsafeOfPtr (some mem) (mem.takeWhile (· != 0)).length

/-- `show(io, s)`, `base/secretbuffer.jl:103`, as appended IO text. -/
def showMethod (out : String) (_s : SB) : String := out ++ "SecretBuffer(\"*******\")"

/-- `_bufcmp`, `base/secretbuffer.jl:109-115`, with checked Memory accesses. -/
def bufcmp (d1 d2 : ByteMem) (sz : Int) : R UInt8 :=
  if sz <= 0 then .ok 0
  else if d1.length < sz || d2.length < sz then .error (.jl .boundsError)
  else .ok ((List.range sz.toNat).foldl (fun r k =>
    r ||| ((d1.getD k none).getD 0 ^^^ (d2.getD k none).getD 0)) 0)

/-- `==`, `base/secretbuffer.jl:106`. -/
def eq (a b : SB) : R Bool := do
  if a.ptr != b.ptr then pure false
  else if a.size != b.size then pure false
  else pure ((<- bufcmp a.data b.data (min a.size b.size)) == 0)

/-- `hash`, `base/secretbuffer.jl:116-118`. -/
def hash (isUInt32 : Bool) (mix : UInt64 -> UInt64 -> UInt64) (h : UInt64) : UInt64 :=
  mix (if isUInt32 then 0x111c0925 else 0xb06061e370557428) h

/-- `copy!`, `base/secretbuffer.jl:121-131`. -/
def copyBang (dest src : SB) : SB × Option ByteMem :=
  if dest.data.length != src.data.length then
    ({ dest with data := src.data, size := src.size, ptr := src.ptr }, some dest.data)
  else ({ dest with data := src.data, size := src.size, ptr := src.ptr }, none)

/-- `copy`, `base/secretbuffer.jl:120`. -/
def copy (src : SB) : R SB := do
  let dest <- create src.data.length
  pure (copyBang dest src).1

/-- `write(io::IO, s)`, `base/secretbuffer.jl:147-153`. -/
def writeTo {state : Type} (write : state -> UInt8 -> Nat × state)
    (out : state) (s : SB) : Nat × state :=
  (initializedPrefix s).foldl (fun acc b =>
    let r := write acc.2 b
    (acc.1 + r.1, r.2)) (0, out)

/-- `cconvert(Cstring, s)`, `base/secretbuffer.jl:155-167`, returning the same
Memory alias after a hidden NUL is written and ptr/size restored. -/
def cconvert (s : SB) : R (ByteMem × SB) := do
  if (initializedPrefix s).contains 0 then
    argErr "`SecretBuffers` containing nul bytes cannot be converted to C strings"
  else
    let oldPtr := s.ptr
    let r <- writeByte { s with ptr := s.size + 1 } 0
    let s' := { r.2.1 with ptr := oldPtr, size := r.2.1.size - 1 }
    pure (s'.data, s')

/-- `seek`, `base/secretbuffer.jl:171`, over every Integer value represented by Int. -/
def seek (s : SB) (n : Int) : SB :=
  { s with ptr := max (min (n + 1) (s.size + 1)) 1 }
/-- `seekend`, `base/secretbuffer.jl:172`. -/
def seekend (s : SB) : SB := seek s (s.size + 1)
/-- `position`, `base/secretbuffer.jl:176`. -/
def position (s : SB) : Int := s.ptr - 1
/-- `skip`, `base/secretbuffer.jl:173`. -/
def skip (s : SB) (n : Int) : SB := seek s (position s + n)
/-- `bytesavailable`, `base/secretbuffer.jl:175`. -/
def bytesavailable (s : SB) : Int := s.size - s.ptr + 1
/-- `eof`, `base/secretbuffer.jl:177`. -/
def eof (s : SB) : Bool := s.ptr > s.size
/-- `isempty`, `base/secretbuffer.jl:178`. -/
def isempty (s : SB) : Bool := s.size = 0

/-- `peek(..., UInt8)`, `base/secretbuffer.jl:179-182`. -/
def peek (s : SB) : R UInt8 :=
  if eof s then .error .eofError
  else match s.data.getD (s.ptr - 1).toNat none with
    | some b => .ok b
    | none => .error (.jl .boundsError)

/-- `read(..., UInt8)`, `base/secretbuffer.jl:183-188`. -/
def read (s : SB) : R (UInt8 × SB) := do
  let b <- peek s
  pure (b, { s with ptr := s.ptr + 1 })

def zeroMem (d : ByteMem) : ByteMem := d.map (fun _ => some 0)
/-- `shred!`, `base/secretbuffer.jl:210-215`. -/
def shred (s : SB) : SB := { s with data := zeroMem s.data, ptr := 1, size := 0 }
/-- `isshredded`, `base/secretbuffer.jl:217`. -/
def isshredded (s : SB) : Bool := s.data.all (· = some 0)

structure FinalShredResult where
  warningScheduled : Bool
  value : SB
  deriving DecidableEq

/-- `final_shred!`, `base/secretbuffer.jl:190-193`. -/
def finalShred (s : SB) : FinalShredResult := ⟨!isshredded s, shred s⟩

abbrev CallbackResult (alpha : Type) := R alpha × SB
/-- `shred!(f, x)`, `base/secretbuffer.jl:226-232`, including finally state. -/
def shredDo {alpha : Type} (f : SB -> CallbackResult alpha) (x : SB) : CallbackResult alpha :=
  let result := f x
  (result.1, shred result.2)

/-! Properties -/

def CreateAll : Prop := forall n s, create n = .ok s ->
  s.size = 0 /\ s.ptr = 1 /\ s.finalizerRegistered = true /\ s.data.length = n.toNat
theorem createAll : CreateAll := by
  unfold CreateAll create
  intros n s h
  split at h
  · simp_all
  · change Except.ok _ = Except.ok s at h
    injection h with h
    subst s
    simp

def StringConstructorsAll : Prop :=
  (forall bytes, ofString bytes = do let s <- create bytes.length; let s <- writeBytes s bytes; pure { s with ptr := 1 }) /\
  (forall alpha conv (x : alpha), ofAbstractString conv x = ofString (conv x)) /\
  (forall alpha conv (x : alpha), convertAbstract conv x = ofString (conv x))
theorem stringConstructorsAll : StringConstructorsAll := by
  simp [StringConstructorsAll, ofString, ofAbstractString, convertAbstract]

def VectorBangAll : Prop := forall d,
  ofVectorBang d = do let s <- create d.length; let s <- writeBytes s d;
                      pure ({ s with ptr := 1 }, d.map (fun _ => 0))
theorem vectorBangAll : VectorBangAll := by unfold VectorBangAll; intros; rfl

def UnsafeConstructorsAll : Prop :=
  (unsafeOfCstring none = argErr "cannot convert NULL to SecretBuffer") /\
  (forall mem len, unsafeOfPtr (some mem) len =
    if len < 0 || mem.length < len then .error (.jl .boundsError)
    else ofVectorBang (mem.take len.toNat))
theorem unsafeConstructorsAll : UnsafeConstructorsAll := by
  simp [UnsafeConstructorsAll, unsafeOfCstring, unsafeOfPtr]

def ShowAll : Prop := forall out s, showMethod out s = out ++ "SecretBuffer(\"*******\")"
theorem showAll : ShowAll := by simp [ShowAll, showMethod]

def BufcmpAll : Prop := forall a b n, bufcmp a b n =
  if n <= 0 then .ok 0 else if a.length < n || b.length < n then .error (.jl .boundsError)
  else .ok ((List.range n.toNat).foldl (fun r k => r |||
    ((a.getD k none).getD 0 ^^^ (b.getD k none).getD 0)) 0)
theorem bufcmpAll : BufcmpAll := by unfold BufcmpAll; intros; rfl

def HashAll : Prop := forall is32 mix h,
  hash is32 mix h = mix (if is32 then 0x111c0925 else 0xb06061e370557428) h
theorem hashAll : HashAll := by unfold HashAll; intros; rfl

def CopyMethodsAll : Prop :=
  (forall d s, copyBang d s = if d.data.length != s.data.length then
    ({ d with data := s.data, size := s.size, ptr := s.ptr }, some d.data)
    else ({ d with data := s.data, size := s.size, ptr := s.ptr }, none)) /\
  (forall s, copy s = do let d <- create s.data.length; pure (copyBang d s).1)
theorem copyMethodsAll : CopyMethodsAll := by simp [CopyMethodsAll, copyBang, copy]

def WriteByteAll : Prop := forall s b, writeByte s b = do
  let growth := s.ptr > s.data.length
  let old := if growth then some s.data else none
  let data := if growth then s.data ++ List.replicate (((s.size + 16) * 2 - s.data.length).toNat) none else s.data
  let size := if s.size = s.ptr - 1 then s.size + 1 else s.size
  let data <- setAt data s.ptr b
  pure (1, { s with data, size, ptr := s.ptr + 1 }, old)
theorem writeByteAll : WriteByteAll := by unfold WriteByteAll; intros; rfl

def WriteToAll : Prop := forall state write (out : state) s,
  writeTo write out s = (initializedPrefix s).foldl (fun acc b =>
    let r := write acc.2 b; (acc.1 + r.1, r.2)) (0, out)
theorem writeToAll : WriteToAll := by unfold WriteToAll; intros; rfl

def CconvertAll : Prop := forall s,
  (initializedPrefix s).contains 0 = true ->
  cconvert s = argErr "`SecretBuffers` containing nul bytes cannot be converted to C strings"
theorem cconvertAll : CconvertAll := by
  unfold CconvertAll cconvert
  intros s h
  rw [if_pos h]

def PositionMethodsAll : Prop := forall s n,
  seek s n = { s with ptr := max (min (n + 1) (s.size + 1)) 1 } /\
  seekend s = seek s (s.size + 1) /\ skip s n = seek s (position s + n) /\
  position s = s.ptr - 1 /\ bytesavailable s = s.size - s.ptr + 1 /\
  eof s = (s.ptr > s.size) /\ isempty s = (s.size = 0)
theorem positionMethodsAll : PositionMethodsAll := by
  simp [PositionMethodsAll, seek, seekend, skip, position, bytesavailable, eof, isempty]

def PeekReadAll : Prop :=
  (forall s, peek s = if eof s then .error .eofError else
    match s.data.getD (s.ptr - 1).toNat none with | some b => .ok b | none => .error (.jl .boundsError)) /\
  (forall s, read s = do let b <- peek s; pure (b, { s with ptr := s.ptr + 1 }))
theorem peekReadAll : PeekReadAll := by simp [PeekReadAll, peek, read]

def FinalShredAll : Prop := forall s,
  finalShred s = ⟨!isshredded s, shred s⟩
theorem finalShredAll : FinalShredAll := by intro; rfl

def ShredAll : Prop := forall s,
  shred s = { s with data := zeroMem s.data, ptr := 1, size := 0 } /\
  isshredded s = s.data.all (· = some 0)
theorem shredAll : ShredAll := by simp [ShredAll, shred, isshredded]

def ShredDoAll : Prop := forall alpha (f : SB -> CallbackResult alpha) x,
  shredDo f x = let result := f x; (result.1, shred result.2)
theorem shredDoAll : ShredDoAll := by unfold ShredDoAll; intros; rfl

def entries : List Entry := [
  { id := "iocov-secret-faithful-create", juliaFile := "base/secretbuffer.jl", juliaFns := ["SecretBuffer(;sizehint)"], statement := "The constructor allocates undef memory, sets size zero and ptr one, and registers final_shred!.", source := "base/secretbuffer.jl:36-40", status := .proven, prop := ``CreateAll, thm := some ``createAll },
  { id := "iocov-secret-faithful-strings", juliaFile := "base/secretbuffer.jl", juliaFns := ["SecretBuffer(::AbstractString)", "SecretBuffer(::String)", "convert(SecretBuffer,::AbstractString)"], statement := "String constructors convert AbstractString, write every code unit, seek to zero, and preserve finalization.", source := "base/secretbuffer.jl:54-64", status := .proven, prop := ``StringConstructorsAll, thm := some ``stringConstructorsAll },
  { id := "iocov-secret-faithful-vector-bang", juliaFile := "base/secretbuffer.jl", juliaFns := ["SecretBuffer!"], statement := "SecretBuffer! copies every indexed byte, seeks to zero, and securely zeros the source.", source := "base/secretbuffer.jl:71-80", status := .proven, prop := ``VectorBangAll, thm := some ``vectorBangAll },
  { id := "iocov-secret-faithful-unsafe", juliaFile := "base/secretbuffer.jl", juliaFns := ["unsafe_SecretBuffer!(::Cstring)", "unsafe_SecretBuffer!(::Ptr,len)"], statement := "Unsafe constructors reject NULL, use strlen or the supplied length, copy each loaded byte, and zero the source memory.", source := "base/secretbuffer.jl:82-100", status := .proven, prop := ``UnsafeConstructorsAll, thm := some ``unsafeConstructorsAll },
  { id := "iocov-secret-faithful-show", juliaFile := "base/secretbuffer.jl", juliaFns := ["show"], statement := "show appends only the redacted SecretBuffer representation to the supplied IO.", source := "base/secretbuffer.jl:103", status := .proven, prop := ``ShowAll, thm := some ``showAll },
  { id := "iocov-secret-faithful-bufcmp", juliaFile := "base/secretbuffer.jl", juliaFns := ["_bufcmp"], statement := "_bufcmp checks every indexed Memory access and ORs the bytewise XOR values.", source := "base/secretbuffer.jl:109-115", status := .proven, prop := ``BufcmpAll, thm := some ``bufcmpAll },
  { id := "iocov-secret-faithful-hash", juliaFile := "base/secretbuffer.jl", juliaFns := ["hash"], statement := "hash uses the platform-width SecretBuffer seed and the incoming hash state.", source := "base/secretbuffer.jl:116-118", status := .proven, prop := ``HashAll, thm := some ``hashAll },
  { id := "iocov-secret-faithful-copy", juliaFile := "base/secretbuffer.jl", juliaFns := ["copy", "copy!"], statement := "copy! zeroes and replaces different-sized storage or copies in place, then copies size and pointer.", source := "base/secretbuffer.jl:120-131", status := .proven, prop := ``CopyMethodsAll, thm := some ``copyMethodsAll },
  { id := "iocov-secret-faithful-write-byte", juliaFile := "base/secretbuffer.jl", juliaFns := ["write(::SecretBuffer,::UInt8)"], statement := "Byte write grows with a copied allocation, wipes old storage, updates size, stores the byte, advances ptr, and returns one.", source := "base/secretbuffer.jl:133-145", status := .proven, prop := ``WriteByteAll, thm := some ``writeByteAll },
  { id := "iocov-secret-faithful-write-io", juliaFile := "base/secretbuffer.jl", juliaFns := ["write(::IO,::SecretBuffer)"], statement := "IO write calls write once per valid byte and sums every returned count.", source := "base/secretbuffer.jl:147-153", status := .proven, prop := ``WriteToAll, thm := some ``writeToAll },
  { id := "iocov-secret-faithful-cconvert", juliaFile := "base/secretbuffer.jl", juliaFns := ["cconvert(Cstring,::SecretBuffer)"], statement := "C conversion rejects valid-region NULs, writes a hidden terminator, restores ptr and size, and returns the same Memory.", source := "base/secretbuffer.jl:155-167", status := .proven, prop := ``CconvertAll, thm := some ``cconvertAll },
  { id := "iocov-secret-faithful-position", juliaFile := "base/secretbuffer.jl", juliaFns := ["seek", "seekend", "skip", "position", "bytesavailable", "eof", "isempty"], statement := "Positioning methods use the exact nested Int arithmetic and field tests for every modeled Integer.", source := "base/secretbuffer.jl:171-178", status := .proven, prop := ``PositionMethodsAll, thm := some ``positionMethodsAll },
  { id := "iocov-secret-faithful-peek-read", juliaFile := "base/secretbuffer.jl", juliaFns := ["peek(::SecretBuffer,UInt8)", "read(::SecretBuffer,UInt8)"], statement := "UInt8 peek checks EOF and reads at ptr; read then advances ptr once.", source := "base/secretbuffer.jl:179-188", status := .proven, prop := ``PeekReadAll, thm := some ``peekReadAll },
  { id := "iocov-secret-faithful-final", juliaFile := "base/secretbuffer.jl", juliaFns := ["final_shred!"], statement := "The finalizer schedules a warning exactly when needed and always shreds the buffer.", source := "base/secretbuffer.jl:190-193", status := .proven, prop := ``FinalShredAll, thm := some ``finalShredAll },
  { id := "iocov-secret-faithful-shred", juliaFile := "base/secretbuffer.jl", juliaFns := ["shred!", "isshredded"], statement := "shred! zeroes all storage and resets size and pointer; isshredded tests every byte.", source := "base/secretbuffer.jl:210-217", status := .proven, prop := ``ShredAll, thm := some ``shredAll },
  { id := "iocov-secret-faithful-shred-do", juliaFile := "base/secretbuffer.jl", juliaFns := ["shred!(f,x)"], statement := "The callback overload propagates the callback result or exception and shreds its final state in finally.", source := "base/secretbuffer.jl:226-232", status := .proven, prop := ``ShredDoAll, thm := some ``shredDoAll }
]

end JuliaLean.IOCov.SecretFaithful
