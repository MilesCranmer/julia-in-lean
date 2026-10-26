import JuliaLean.IOCov.Common

set_option linter.unusedSimpArgs false

/-!
Models of `base/libc.jl` at master `bbfa0ce4150` (Unix branches). Each C call is
an argument carrying the C function's result; the models mirror the Julia code
around it: integer conversions, NULL and error-code checks, and the
conversions of the result.
-/

namespace JuliaLean.IOCov.Libc

open JuliaLean JuliaLean.IOCov

/-! ## `RawFD`, `dup`, `show`, lines 35-51 -/

/-- `RawFD(fd::Integer) = bitcast(RawFD, Cint(fd))`, `base/libc.jl:35`. -/
def rawFD (fd : Int) : R Int := toInt .i32 fd
/-- `RawFD(fd::RawFD) = fd`, `base/libc.jl:36`. -/
def rawFDId (fd : Int) : Int := fd
/-- `cconvert(::Type{Cint}, fd::RawFD) = bitcast(Cint, fd)`, `base/libc.jl:37`. -/
def cconvertCint (fd : Int) : Int := fd

/-- `dup(x::RawFD)`, `base/libc.jl:46`: the result of C `dup` is returned unchecked. -/
def dup1 (cdup : Int → Int) (x : Int) : R Int := .ok (cdup x)
/-- `dup(src, target)`, `base/libc.jl:47-49`: `systemerror("dup", -1 == dup2(...))`. -/
def dup2 (cdup2 : Int → Int → Int) (src target : Int) : R Unit :=
  systemerror "dup" (-1 == cdup2 src target)

/-- `show(io, fd::RawFD) = print(io, "RawFD(", bitcast(Int32, fd), ')')`, `base/libc.jl:51`. -/
def showRawFD (fd : Int) : String := "RawFD(" ++ toString fd ++ ")"

def RawFDCorrect : Prop :=
  (∀ fd : Int, rawFD fd = (if -2147483648 ≤ fd ∧ fd ≤ 2147483647 then .ok fd
      else .error (.jl (.inexactError "Int32")))) ∧
  (∀ fd, rawFDId fd = fd ∧ cconvertCint fd = fd) ∧
  (∀ cdup x, dup1 cdup x = .ok (cdup x)) ∧
  (∀ cdup2 src target, dup2 cdup2 src target =
      if cdup2 src target = -1 then .error (.systemError "dup") else .ok ()) ∧
  (∀ fd, showRawFD fd = "RawFD(" ++ toString fd ++ ")")

theorem rawFDCorrect : RawFDCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro fd
    by_cases h : -2147483648 ≤ fd ∧ fd ≤ 2147483647
    · rw [if_pos h]; exact toInt_i32 fd h.1 h.2
    · rw [if_neg h]; exact toInt_err .i32 fd (by simpa using h)
  · intro fd; exact ⟨rfl, rfl⟩
  · intros; rfl
  · intro cdup2 src target
    unfold dup2 systemerror
    by_cases h : cdup2 src target = -1
    · simp [h]
    · have h' : ¬ (-1 = cdup2 src target) := fun e => h e.symm
      simp [h, h']
  · intros; rfl

/-! ## `FILE`, lines 123-147 -/

/-- `modestr(r::Bool, w::Bool)`, `base/libc.jl:124`. -/
def modestr (r w : Bool) : R String :=
  if r then (if w then .ok "r+" else .ok "r")
  else if w then .ok "w" else argErr "neither readable nor writable"

/-- `modestr(s::IO) = modestr(isreadable(s), iswritable(s))`, `base/libc.jl:123`. -/
def modestrIO (isreadable iswritable : Bool) : R String := modestr isreadable iswritable

/-- `FILE(fd::RawFD, mode)`, `base/libc.jl:126-130`; `fdopen` returns a pointer (0 = NULL). -/
def fileOfFd (fdopen : Int → String → Nat) (fd : Int) (mode : String) : R Nat := do
  let p := fdopen fd mode
  systemerror "fdopen" (p == 0)
  pure p

/-- `seek(h::FILE, offset)`, `base/libc.jl:141-145`: `offset` is converted to `Clong`. -/
def seekFILE (fseek : Nat → Int → Int) (h : Nat) (offset : Int) : R Nat := do
  let off ← toInt .i64 offset
  systemerror "fseek" (fseek h off != 0)
  pure h

/-- `FILE(s::IO)`, `base/libc.jl:132-136`: `dup` is unchecked, then `fdopen` and `seek`. -/
def fileOfIO (cdup : Int → Int) (fdopen : Int → String → Nat) (fseek : Nat → Int → Int)
    (fd : Int) (r w : Bool) (pos : Int) : R Nat := do
  let d ← rawFD fd
  let d' ← dup1 cdup d
  let m ← modestrIO r w
  let f ← fileOfFd fdopen d' m
  seekFILE fseek f pos

/-- `unsafe_convert(Ptr, f::FILE) = convert(T, f.ptr)`, `base/libc.jl:138`. -/
def unsafeConvertFILE (ptr : Nat) : Nat := ptr
/-- `close(f::FILE)`, `base/libc.jl:139`. -/
def closeFILE (fclose : Nat → Int) (f : Nat) : R Unit := systemerror "fclose" (fclose f != 0)
/-- `position(h::FILE)`, `base/libc.jl:147`: `ftell`'s result, unchecked. -/
def positionFILE (ftell : Nat → Int) (h : Nat) : Int := ftell h
/-- `flush_cstdio()`, `base/libc.jl:156`: one call to `jl_flush_cstdio`. -/
def flushCstdio (flush : Unit → Unit) : Unit := flush ()

/-- `dup` duplicates the descriptor; like `dup(src, target)`, a failing C call (`-1`)
should be reported rather than returned as a descriptor. -/
def DupChecked : Prop :=
  ∀ (cdup : Int → Int) x, cdup x = -1 → dup1 cdup x = .error (.systemError "dup")

theorem dupChecked_refuted : ¬ DupChecked := by
  intro h
  have := h (fun _ => -1) 12345 rfl
  simp [dup1] at this

def FileCorrect : Prop :=
  (∀ r w, modestr r w = .ok (if r then (if w then "r+" else "r") else "w") ∨
      (r = false ∧ w = false ∧ modestr r w = argErr "neither readable nor writable")) ∧
  (∀ r w, modestrIO r w = modestr r w) ∧
  (∀ fdopen fd mode, fileOfFd fdopen fd mode =
      if fdopen fd mode = 0 then .error (.systemError "fdopen") else .ok (fdopen fd mode)) ∧
  (∀ fseek h off, -9223372036854775808 ≤ off → off ≤ 9223372036854775807 →
      seekFILE fseek h off = if fseek h off = 0 then .ok h else .error (.systemError "fseek")) ∧
  (∀ cdup fdopen fseek fd pos, -2147483648 ≤ fd → fd ≤ 2147483647 →
      fileOfIO cdup fdopen fseek fd false false pos = argErr "neither readable nor writable") ∧
  (∀ p, unsafeConvertFILE p = p) ∧
  (∀ fclose f, closeFILE fclose f = if fclose f = 0 then .ok () else .error (.systemError "fclose")) ∧
  (∀ ftell h, positionFILE ftell h = ftell h) ∧
  (∀ fl, flushCstdio fl = fl ())

theorem fileCorrect : FileCorrect := by
  refine ⟨?_, fun _ _ => rfl, ?_, ?_, ?_, fun _ => rfl, ?_, fun _ _ => rfl, fun _ => rfl⟩
  · intro r w; cases r <;> cases w <;> simp [modestr]
  · intro fdopen fd mode
    by_cases h : fdopen fd mode = 0 <;> simp [fileOfFd, systemerror, h, bind, Except.bind, pure, Except.pure]
  · intro fseek h off h1 h2
    by_cases hz : fseek h off = 0 <;>
      simp [seekFILE, systemerror, toInt_i64 off h1 h2, hz, bind, Except.bind, pure, Except.pure]
  · intro cdup fdopen fseek fd pos h1 h2
    simp [fileOfIO, rawFD, dup1, toInt_i32 fd h1 h2, modestrIO, modestr, argErr, bind, Except.bind,
      pure, Except.pure]
  · intro fclose f
    by_cases h : fclose f = 0 <;> simp [closeFILE, systemerror, h]

/-! ## `systemsleep`, `TimeVal`, `TmStruct`, lines 162-226 -/

/-- `round(UInt32, x)` of a real `x` given as the exact rational `x`: `InexactError`
outside `0:typemax(UInt32)` (rounding to nearest, ties to even). -/
def roundUInt32 (x : Int) : R Int := toInt .u32 x

/-- `systemsleep(s::Real)` on Unix, `base/libc.jl:162`: `usleep(round(UInt32, s*1e6))`,
with `us = s*1e6` already rounded to an integer. -/
def systemsleep (usleep : Int → Int) (us : Int) : R Int := do
  let n ← roundUInt32 us
  pure (usleep n)

/-- `TimeVal()`, `base/libc.jl:187-192`: `error` when `jl_gettimeofday` fails. -/
def timeVal (gettimeofday : Unit → Int × (Int × Int)) : R (Int × Int) :=
  let (status, tv) := gettimeofday ()
  if status != 0 then .error (.errorException "unable to determine current time: ")
  else .ok tv

/-- The 14 `Int32` fields of `TmStruct`. -/
abbrev Tm := List Int

/-- `TmStruct(sec, ..., isdst)`, `base/libc.jl:217-218`: fields converted to `Int32`,
the 5 padding fields zero. -/
def tmStruct9 (fs : List Int) : R Tm := do
  let cs ← fs.mapM (toInt .i32)
  pure (cs ++ [0, 0, 0, 0, 0])
/-- `TmStruct()`, `base/libc.jl:219`. -/
def tmStruct0 : Tm := List.replicate 14 0
/-- `TmStruct(t::Real)`, `base/libc.jl:220-226`: `floor(t)` converted to `Int` for
`localtime_r`, which fills the struct. `t` is given as `floor(t)` (`none` for
NaN/Inf). -/
def tmStructOfTime (localtime : Int → Tm) (floort : Option Int) : R Tm :=
  match floort with
  | none => .error (.jl (.inexactError "Int64"))
  | some t => do let n ← toInt .i64 t; pure (localtime n)

/-- Documented: `systemsleep(s)` "suspends execution for `s` seconds", for any
nonnegative duration (`us = s*1e6` microseconds). -/
def SystemsleepAny : Prop :=
  ∀ (usleep : Int → Int) (us : Int), 0 ≤ us → ∃ r, systemsleep usleep us = .ok r

theorem systemsleepAny_refuted : ¬ SystemsleepAny := by
  intro h
  obtain ⟨r, hr⟩ := h (fun _ => 0) 4295000000 (by decide)
  simp [systemsleep, roundUInt32, toInt_u32_neg 4295000000 (Or.inr (by decide)), bind,
    Except.bind] at hr

def TimeCorrect : Prop :=
  (∀ usleep us, 0 ≤ us → us ≤ 4294967295 → systemsleep usleep us = .ok (usleep us)) ∧
  (∀ usleep us, (us < 0 ∨ 4294967295 < us) →
      systemsleep usleep us = .error (.jl (.inexactError "UInt32"))) ∧
  (∀ g, timeVal g = if (g ()).1 = 0 then .ok (g ()).2
      else .error (.errorException "unable to determine current time: ")) ∧
  (∀ fs : List Int, (∀ x ∈ fs, -2147483648 ≤ x ∧ x ≤ 2147483647) →
      tmStruct9 fs = .ok (fs ++ [0, 0, 0, 0, 0])) ∧
  tmStruct0.length = 14 ∧ (∀ x ∈ tmStruct0, x = 0) ∧
  (∀ lt t, -9223372036854775808 ≤ t → t ≤ 9223372036854775807 →
      tmStructOfTime lt (some t) = .ok (lt t)) ∧
  (∀ lt, tmStructOfTime lt none = .error (.jl (.inexactError "Int64")))

theorem mapM_toInt_ok (fs : List Int) (h : ∀ x ∈ fs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    fs.mapM (toInt .i32) = .ok fs := by
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, -2147483648 ≤ y ∧ y ≤ 2147483647 := fun y hy => h y (by simp [hy])
    simp only [List.mapM_cons]
    rw [toInt_i32 x hx.1 hx.2, ih hxs]
    rfl

theorem timeCorrect : TimeCorrect := by
  refine ⟨?_, ?_, ?_, ?_, rfl, fun x hx => List.eq_of_mem_replicate hx, ?_, fun _ => rfl⟩
  · intro usleep us h1 h2
    simp [systemsleep, roundUInt32, toInt_u32 us h1 h2, bind, Except.bind, pure, Except.pure]
  · intro usleep us h
    simp [systemsleep, roundUInt32, toInt_u32_neg us h, bind, Except.bind]
  · intro g
    unfold timeVal
    rcases g () with ⟨s, tv⟩
    by_cases h : s = 0 <;> simp [h]
  · intro fs h
    simp [tmStruct9, mapM_toInt_ok fs h, bind, Except.bind, pure, Except.pure]
  · intro lt t h1 h2
    simp [tmStructOfTime, toInt_i64 t h1 h2, bind, Except.bind, pure, Except.pure]

/-! ## `strftime`, `strptime`, `time`, lines 236-325 -/

/-- `strftime(fmt, tm::TmStruct)`, `base/libc.jl:239-245`: `wcsftime` writes into a
buffer of 128 wide characters and returns 0 when the result (with its NUL) does not
fit, in which case `""` is returned. `wcsftime` is given by the full formatted text. -/
def strftimeTm (format : List Char) : List Char :=
  let n := if format.length + 1 ≤ 128 then format.length else 0
  if n == 0 then [] else format.take n

/-- `strftime(fmt, t::Real) = strftime(fmt, TmStruct(t))`, `base/libc.jl:237`. -/
def strftimeReal (localtime : Int → Tm) (fmtText : Tm → List Char) (t : Int) : R (List Char) := do
  let tm ← tmStructOfTime localtime (some t)
  pure (strftimeTm (fmtText tm))

/-- `strftime(t) = strftime("%c", t)`, `base/libc.jl:236`. -/
def strftime1 (localtime : Int → Tm) (cText : Tm → List Char) (t : Int) : R (List Char) :=
  strftimeReal localtime cText t

/-- Documented: `strftime` returns the text formatted per the C library. -/
def StrftimeFormats : Prop :=
  ∀ format : List Char, strftimeTm format = format

theorem strftimeFormats_refuted : ¬ StrftimeFormats := by
  intro h
  have := congrArg List.length (h (List.replicate 128 'x'))
  simp [strftimeTm] at this

def StrftimeWrappers : Prop :=
  (∀ format : List Char, format.length < 128 → strftimeTm format = format) ∧
  (∀ lt f t, -9223372036854775808 ≤ t → t ≤ 9223372036854775807 →
      strftimeReal lt f t = .ok (strftimeTm (f (lt t)))) ∧
  (∀ lt f t, strftime1 lt f t = strftimeReal lt f t)

theorem strftimeWrappers : StrftimeWrappers := by
  refine ⟨?_, ?_, fun _ _ _ => rfl⟩
  · intro format h
    have h1 : format.length + 1 ≤ 128 := by omega
    by_cases h0 : format.length = 0
    · simp [strftimeTm, h1, h0, List.length_eq_zero_iff.mp h0]
    · simp [strftimeTm, h1, h0]
  · intro lt f t h1 h2
    simp [strftimeReal, tmStructOfTime, toInt_i64 t h1 h2, bind, Except.bind, pure, Except.pure]

/-- `strptime(fmt, timestr)`, `base/libc.jl:258-307` (non-Apple): `strptime` fills a
zeroed `TmStruct`; a NULL return throws. The C call is `cstrptime tm0 = (ok, tm)`. -/
def strptime (cstrptime : Tm → Bool × Tm) : R Tm :=
  let (ok, tm) := cstrptime tmStruct0
  if !ok then argErr "invalid arguments" else .ok tm

/-- `strptime(timestr) = strptime("%c", timestr)`, `base/libc.jl:257`. -/
def strptime1 (cstrptimeC : Tm → Bool × Tm) : R Tm := strptime cstrptimeC

/-- `time(tm::TmStruct) = Float64(mktime(tm))`, `base/libc.jl:316`. -/
def timeTm (mktime : Tm → Int) (tm : Tm) : Int := mktime tm
/-- `time() = jl_clock_now()`, `base/libc.jl:325`. -/
def timeNow (clock : Unit → Float) : Float := clock ()

def StrptimeCorrect : Prop :=
  (∀ c, strptime c = if (c tmStruct0).1 then .ok (c tmStruct0).2 else argErr "invalid arguments") ∧
  (∀ c, strptime1 c = strptime c) ∧
  (∀ mk tm, timeTm mk tm = mk tm) ∧ (∀ c, timeNow c = c ())

theorem strptimeCorrect : StrptimeCorrect := by
  refine ⟨?_, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  intro c; unfold strptime; rcases c tmStruct0 with ⟨ok, tm⟩; cases ok <;> rfl

/-! ## Process and host queries, errno, lines 334-375 -/

/-- `getpid() = uv_os_getpid()`, `base/libc.jl:334`. -/
def getpid (c : Unit → Int) : Int := c ()

/-- `gethostname()`, `base/libc.jl:343-352`: a 256-byte buffer, `systemerror` on a
nonzero return, then the bytes up to the first NUL. -/
def gethostname (c : Nat → Int × List UInt8) : R (List UInt8) := do
  let (err, hn) := c 256
  systemerror "gethostname" (err != 0)
  pure (hn.takeWhile (· != 0))

/-- `errno() = jl_errno()` and `errno(e) = jl_set_errno(Cint(e))`, `base/libc.jl:366-367`. -/
def errnoGet (state : Int) : Int := state
def errnoSet (e : Int) : R Int := toInt .i32 e

/-- `strerror(e::Integer) = unsafe_string(strerror(Int32(e)))`, `base/libc.jl:374`. -/
def strerror (c : Int → List UInt8) (e : Int) : R (List UInt8) := do
  let x ← toInt .i32 e
  pure (c x)
/-- `strerror() = strerror(errno())`, `base/libc.jl:375`. -/
def strerror0 (c : Int → List UInt8) (errno : Int) : R (List UInt8) := strerror c (errnoGet errno)

def ProcessQueriesCorrect : Prop :=
  (∀ c, getpid c = c ()) ∧
  (∀ c, gethostname c = if (c 256).1 = 0 then .ok ((c 256).2.takeWhile (· != 0))
      else .error (.systemError "gethostname")) ∧
  (∀ s, errnoGet s = s) ∧
  (∀ e, errnoSet e = toInt .i32 e) ∧
  (∀ c e, -2147483648 ≤ e → e ≤ 2147483647 → strerror c e = .ok (c e)) ∧
  (∀ c e, strerror0 c e = strerror c e)

theorem processQueriesCorrect : ProcessQueriesCorrect := by
  refine ⟨fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl, ?_, fun _ _ => rfl⟩
  · intro c; unfold gethostname; rcases c 256 with ⟨err, hn⟩
    by_cases h : err = 0 <;> simp [systemerror, h, bind, Except.bind, pure, Except.pure]
  · intro c e h1 h2
    simp [strerror, toInt_i32 e h1 h2, bind, Except.bind, pure, Except.pure]

/-! ## Memory, lines 423-449 -/

/-- `free(p::Ptr)`, `free(p::Cstring)`, `free(p::Cwstring)`, `base/libc.jl:423-425`:
each converts to `Ptr{Cvoid}` and calls C `free` on the same address. -/
def free (cfree : Nat → Unit) (p : Nat) : Unit := cfree p
def freeCstring (cfree : Nat → Unit) (p : Nat) : Unit := free cfree p
def freeCwstring (cfree : Nat → Unit) (p : Nat) : Unit := free cfree p

/-- `malloc(size::Integer)`, `base/libc.jl:432`: `size` converted to `Csize_t`. -/
def malloc (cmalloc : Int → Nat) (size : Int) : R Nat := do
  let n ← toInt .u64 size
  pure (cmalloc n)
/-- `realloc(p, size)`, `base/libc.jl:442`. -/
def realloc (crealloc : Nat → Int → Nat) (p : Nat) (size : Int) : R Nat := do
  let n ← toInt .u64 size
  pure (crealloc p n)
/-- `calloc(num, size)`, `base/libc.jl:449`. -/
def calloc (ccalloc : Int → Int → Nat) (num size : Int) : R Nat := do
  let a ← toInt .u64 num
  let b ← toInt .u64 size
  pure (ccalloc a b)

def MemoryCorrect : Prop :=
  (∀ c p, free c p = c p ∧ freeCstring c p = c p ∧ freeCwstring c p = c p) ∧
  (∀ c size, 0 ≤ size → size ≤ 18446744073709551615 → malloc c size = .ok (c size)) ∧
  (∀ c size, size < 0 → malloc c size = .error (.jl (.inexactError "UInt64"))) ∧
  (∀ c p size, 0 ≤ size → size ≤ 18446744073709551615 → realloc c p size = .ok (c p size)) ∧
  (∀ c a b, 0 ≤ a → a ≤ 18446744073709551615 → 0 ≤ b → b ≤ 18446744073709551615 →
      calloc c a b = .ok (c a b))

theorem memoryCorrect : MemoryCorrect := by
  refine ⟨fun _ _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro c size h1 h2; simp [malloc, toInt_u64 size h1 h2, bind, Except.bind, pure, Except.pure]
  · intro c size h; simp [malloc, toInt_u64_neg size h, bind, Except.bind]
  · intro c p size h1 h2; simp [realloc, toInt_u64 size h1 h2, bind, Except.bind, pure, Except.pure]
  · intro c a b h1 h2 h3 h4
    simp [calloc, toInt_u64 a h1 h2, toInt_u64 b h3 h4, bind, Except.bind, pure, Except.pure]

/-! ## Randomness, lines 456-483 -/

/-- `getrandom!(A)`, `base/libc.jl:456-461`: `uv_random` fills `A`; a negative return
throws, otherwise `A` (filled) is returned. -/
def getrandom (uvRandom : Nat → Int × List UInt8) (len : Nat) : R (List UInt8) := do
  let (ret, bytes) := uvRandom len
  uvError "getrandom" ret
  pure bytes

/-- `_make_uint64_seed()`, `base/libc.jl:462`: eight random bytes read as a `UInt64`
(little-endian). -/
def makeSeed (uvRandom : Nat → Int × List UInt8) : R Nat := do
  let b ← getrandom uvRandom 8
  pure (b.foldr (fun x acc => x.toNat + 256 * acc) 0)

/-- `rand() = jl_rand() % UInt32`, `base/libc.jl:472`. -/
def rand (jlRand : Nat) : Nat := jlRand % 2 ^ 32
/-- `rand(::Type{UInt32}) = rand()`, `base/libc.jl:473`. -/
def randU32 (jlRand : Nat) : Nat := rand jlRand
/-- `rand(::Type{Float64}) = rand() * 2.0^-32`, `base/libc.jl:474`: the product is exact,
so the value is the rational `rand() / 2^32`, given here as numerator and denominator. -/
def randF64 (jlRand : Nat) : Nat × Nat := (rand jlRand, 2 ^ 32)

/-- `srand(seed)`, `base/libc.jl:481-483`: `jl_srand(seed % UInt64)`. -/
def srand (seed : Int) : Int := wrapTo .u64 seed

def RandomCorrect : Prop :=
  (∀ u len, getrandom u len = if (u len).1 < 0 then .error (.uvError "getrandom") else .ok (u len).2) ∧
  (∀ x, rand x < 2 ^ 32 ∧ randU32 x = rand x) ∧
  (∀ x, (randF64 x).1 < (randF64 x).2) ∧
  (∀ s, 0 ≤ srand s ∧ srand s < 2 ^ 64 ∧ (srand s - s) % 2 ^ 64 = 0)

theorem randomCorrect : RandomCorrect := by
  refine ⟨?_, fun x => ⟨Nat.mod_lt _ (by decide), rfl⟩, fun x => Nat.mod_lt _ (by decide), ?_⟩
  · intro u len; unfold getrandom; rcases u len with ⟨ret, b⟩
    by_cases h : ret < 0 <;> simp [uvError, h, bind, Except.bind, pure, Except.pure]
  · intro s
    simp only [srand, wrapTo, wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max]
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega

/-! ## `mkfifo`, passwd and group records, lines 495-608 -/

/-- `mkfifo(path, mode)`, `base/libc.jl:495-510` (Unix): `systemerror` when `mkfifo`
returns -1, else `path`. `mode` is converted to `Cmode_t` (`UInt32`). -/
def mkfifo (cmkfifo : List UInt8 → Int → Int) (path : List UInt8) (mode : Int) : R (List UInt8) := do
  let m ← toInt .u32 mode
  systemerror "mkfifo" (cmkfifo path m == -1)
  pure path

/-- C `passwd` record as read back from libuv. -/
structure Cpasswd where
  username : CStr
  uid : Nat
  gid : Nat
  shell : CStr
  homedir : CStr
  gecos : CStr
  deriving DecidableEq, Repr

/-- `Cpasswd()`, `base/libc.jl:519`. -/
def cpasswd0 : Cpasswd := ⟨none, 2 ^ 64 - 1, 2 ^ 64 - 1, none, none, none⟩

structure Cgroup where
  groupname : CStr
  gid : Nat
  mem : Option (List (List UInt8))
  deriving DecidableEq, Repr

/-- `Cgroup()`, `base/libc.jl:525`. -/
def cgroup0 : Cgroup := ⟨none, 2 ^ 64 - 1, none⟩

structure Passwd where
  username : List UInt8
  uid : Nat
  gid : Nat
  shell : List UInt8
  homedir : List UInt8
  gecos : List UInt8
  deriving DecidableEq, Repr

/-- The `Passwd(...)` conversion shared by `getpw` and `getpwuid`. -/
def passwdOf (pd : Cpasswd) : Passwd :=
  ⟨cstrOrEmpty pd.username, pd.uid, pd.gid, cstrOrEmpty pd.shell, cstrOrEmpty pd.homedir,
    cstrOrEmpty pd.gecos⟩

/-- `getpw()`, `base/libc.jl:543-559`. -/
def getpw (c : Cpasswd → Int × Cpasswd) : R Passwd := do
  let (ret, pd) := c cpasswd0
  uvError "getpw" ret
  pure (passwdOf pd)

/-- `getpwuid(uid, throw_error)`, `base/libc.jl:561-579`; `nothing` is `none`. -/
def getpwuid (c : Cpasswd → Nat → Int × Cpasswd) (uid : Nat) (throwError : Bool) :
    R (Option Passwd) := do
  let (ret, pd) := c cpasswd0 uid
  if ret != 0 then
    if throwError then uvError "getpwuid" ret
    pure none
  else pure (some (passwdOf pd))

structure Group where
  groupname : List UInt8
  gid : Nat
  mem : List (List UInt8)
  deriving DecidableEq, Repr

/-- `getgrgid(gid, throw_error)`, `base/libc.jl:581-604`: members are read until the
NULL entry (`mem` lists them; `none` is a NULL `mem` array). -/
def getgrgid (c : Cgroup → Nat → Int × Cgroup) (gid : Nat) (throwError : Bool) :
    R (Option Group) := do
  let (ret, gp) := c cgroup0 gid
  if ret != 0 then
    if throwError then uvError "getgrgid" ret
    pure none
  else
    let members := match gp.mem with | none => [] | some ms => ms
    pure (some ⟨cstrOrEmpty gp.groupname, gp.gid, members⟩)

/-- `getuid`, `geteuid`, `getegid`, `base/libc.jl:606-608` (Unix): one C call each. -/
def getuid (c : Unit → Nat) : Nat := c ()
def geteuid (c : Unit → Nat) : Nat := c ()
def getegid (c : Unit → Nat) : Nat := c ()

def UsersCorrect : Prop :=
  (∀ c path mode, 0 ≤ mode → mode ≤ 4294967295 →
      mkfifo c path mode = if c path mode = -1 then .error (.systemError "mkfifo") else .ok path) ∧
  cpasswd0.username = none ∧ cpasswd0.uid = 2 ^ 64 - 1 ∧ cgroup0.mem = none ∧
  (∀ c, getpw c = if (c cpasswd0).1 < 0 then .error (.uvError "getpw") else .ok (passwdOf (c cpasswd0).2)) ∧
  (∀ pd : Cpasswd, pd.username = none → (passwdOf pd).username = []) ∧
  (∀ c uid, (c cpasswd0 uid).1 ≠ 0 → getpwuid c uid false = .ok none) ∧
  (∀ c uid, (c cpasswd0 uid).1 = 0 → getpwuid c uid true = .ok (some (passwdOf (c cpasswd0 uid).2))) ∧
  (∀ c gid, (c cgroup0 gid).1 < 0 → getgrgid c gid true = .error (.uvError "getgrgid")) ∧
  (∀ c gid, (c cgroup0 gid).1 = 0 → (c cgroup0 gid).2.mem = none →
      getgrgid c gid false = .ok (some ⟨cstrOrEmpty (c cgroup0 gid).2.groupname, (c cgroup0 gid).2.gid, []⟩)) ∧
  (∀ c, getuid c = c () ∧ geteuid c = c () ∧ getegid c = c ())

theorem usersCorrect : UsersCorrect := by
  refine ⟨?_, rfl, rfl, rfl, ?_, fun pd h => by simp [passwdOf, cstrOrEmpty, h], ?_, ?_, ?_, ?_,
    fun _ => ⟨rfl, rfl, rfl⟩⟩
  · intro c path mode h1 h2
    by_cases h : c path mode = -1 <;>
      simp [mkfifo, systemerror, toInt_u32 mode h1 h2, h, bind, Except.bind, pure, Except.pure]
  · intro c; unfold getpw; rcases c cpasswd0 with ⟨ret, pd⟩
    by_cases h : ret < 0 <;> simp [uvError, h, bind, Except.bind, pure, Except.pure]
  · intro c uid h; unfold getpwuid; rcases hc : c cpasswd0 uid with ⟨ret, pd⟩
    rw [hc] at h; simp at h; simp [h, bind, Except.bind, pure, Except.pure]
  · intro c uid h; unfold getpwuid; rcases hc : c cpasswd0 uid with ⟨ret, pd⟩
    rw [hc] at h; simp at h; simp [h, bind, Except.bind, pure, Except.pure]
  · intro c gid h; unfold getgrgid; rcases hc : c cgroup0 gid with ⟨ret, gp⟩
    rw [hc] at h; simp at h
    have : ret ≠ 0 := by omega
    simp [this, uvError, h, bind, Except.bind, pure, Except.pure]
  · intro c gid h hm; unfold getgrgid; rcases hc : c cgroup0 gid with ⟨ret, gp⟩
    rw [hc] at h hm; simp at h hm; simp [h, hm, bind, Except.bind, pure, Except.pure]


/-! ## Per-method properties -/

def RawFDCorrect_1 : Prop :=
  (∀ fd : Int, rawFD fd = (if -2147483648 ≤ fd ∧ fd ≤ 2147483647 then .ok fd
      else .error (.jl (.inexactError "Int32"))))
theorem rawFDCorrect_1 : RawFDCorrect_1 := by
  have h := rawFDCorrect
  exact h.1

def RawFDCorrect_2 : Prop :=
  (∀ fd, rawFDId fd = fd ∧ cconvertCint fd = fd)
theorem rawFDCorrect_2 : RawFDCorrect_2 := by
  have h := rawFDCorrect
  exact h.2.1

def RawFDCorrect_3 : Prop :=
  (∀ cdup x, dup1 cdup x = .ok (cdup x))
theorem rawFDCorrect_3 : RawFDCorrect_3 := by
  have h := rawFDCorrect
  exact h.2.2.1

def RawFDCorrect_4 : Prop :=
  (∀ cdup2 src target, dup2 cdup2 src target =
      if cdup2 src target = -1 then .error (.systemError "dup") else .ok ())
theorem rawFDCorrect_4 : RawFDCorrect_4 := by
  have h := rawFDCorrect
  exact h.2.2.2.1

def RawFDCorrect_5 : Prop :=
  (∀ fd, showRawFD fd = "RawFD(" ++ toString fd ++ ")")
theorem rawFDCorrect_5 : RawFDCorrect_5 := by
  have h := rawFDCorrect
  exact h.2.2.2.2

def FileCorrect_1 : Prop :=
  (∀ r w, modestr r w = .ok (if r then (if w then "r+" else "r") else "w") ∨
      (r = false ∧ w = false ∧ modestr r w = argErr "neither readable nor writable"))
theorem fileCorrect_1 : FileCorrect_1 := by
  have h := fileCorrect
  exact h.1

def FileCorrect_2 : Prop :=
  (∀ r w, modestrIO r w = modestr r w)
theorem fileCorrect_2 : FileCorrect_2 := by
  have h := fileCorrect
  exact h.2.1

def FileCorrect_3 : Prop :=
  (∀ fdopen fd mode, fileOfFd fdopen fd mode =
      if fdopen fd mode = 0 then .error (.systemError "fdopen") else .ok (fdopen fd mode))
theorem fileCorrect_3 : FileCorrect_3 := by
  have h := fileCorrect
  exact h.2.2.1

def FileCorrect_4 : Prop :=
  (∀ fseek h off, -9223372036854775808 ≤ off → off ≤ 9223372036854775807 →
      seekFILE fseek h off = if fseek h off = 0 then .ok h else .error (.systemError "fseek"))
theorem fileCorrect_4 : FileCorrect_4 := by
  have h := fileCorrect
  exact h.2.2.2.1

def FileCorrect_5 : Prop :=
  (∀ cdup fdopen fseek fd pos, -2147483648 ≤ fd → fd ≤ 2147483647 →
      fileOfIO cdup fdopen fseek fd false false pos = argErr "neither readable nor writable")
theorem fileCorrect_5 : FileCorrect_5 := by
  have h := fileCorrect
  exact h.2.2.2.2.1

def FileCorrect_6 : Prop :=
  (∀ p, unsafeConvertFILE p = p)
theorem fileCorrect_6 : FileCorrect_6 := by
  have h := fileCorrect
  exact h.2.2.2.2.2.1

def FileCorrect_7 : Prop :=
  (∀ fclose f, closeFILE fclose f = if fclose f = 0 then .ok () else .error (.systemError "fclose"))
theorem fileCorrect_7 : FileCorrect_7 := by
  have h := fileCorrect
  exact h.2.2.2.2.2.2.1

def FileCorrect_8 : Prop :=
  (∀ ftell h, positionFILE ftell h = ftell h)
theorem fileCorrect_8 : FileCorrect_8 := by
  have h := fileCorrect
  exact h.2.2.2.2.2.2.2.1

def FileCorrect_9 : Prop :=
  (∀ fl, flushCstdio fl = fl ())
theorem fileCorrect_9 : FileCorrect_9 := by
  have h := fileCorrect
  exact h.2.2.2.2.2.2.2.2

def TimeCorrect_1 : Prop :=
  (∀ usleep us, 0 ≤ us → us ≤ 4294967295 → systemsleep usleep us = .ok (usleep us))
theorem timeCorrect_1 : TimeCorrect_1 := by
  have h := timeCorrect
  exact h.1

def TimeCorrect_2 : Prop :=
  (∀ usleep us, (us < 0 ∨ 4294967295 < us) →
      systemsleep usleep us = .error (.jl (.inexactError "UInt32")))
theorem timeCorrect_2 : TimeCorrect_2 := by
  have h := timeCorrect
  exact h.2.1

def TimeCorrect_3 : Prop :=
  (∀ g, timeVal g = if (g ()).1 = 0 then .ok (g ()).2
      else .error (.errorException "unable to determine current time: "))
theorem timeCorrect_3 : TimeCorrect_3 := by
  have h := timeCorrect
  exact h.2.2.1

def TimeCorrect_4 : Prop :=
  (∀ fs : List Int, (∀ x ∈ fs, -2147483648 ≤ x ∧ x ≤ 2147483647) →
      tmStruct9 fs = .ok (fs ++ [0, 0, 0, 0, 0])) ∧
  tmStruct0.length = 14
theorem timeCorrect_4 : TimeCorrect_4 := by
  have h := timeCorrect
  exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩

def TimeCorrect_5 : Prop :=
  (∀ x ∈ tmStruct0, x = 0)
theorem timeCorrect_5 : TimeCorrect_5 := by
  have h := timeCorrect
  exact h.2.2.2.2.2.1

def TimeCorrect_6 : Prop :=
  (∀ lt t, -9223372036854775808 ≤ t → t ≤ 9223372036854775807 →
      tmStructOfTime lt (some t) = .ok (lt t))
theorem timeCorrect_6 : TimeCorrect_6 := by
  have h := timeCorrect
  exact h.2.2.2.2.2.2.1

def TimeCorrect_7 : Prop :=
  (∀ lt, tmStructOfTime lt none = .error (.jl (.inexactError "Int64")))
theorem timeCorrect_7 : TimeCorrect_7 := by
  have h := timeCorrect
  exact h.2.2.2.2.2.2.2

def StrftimeWrappers_1 : Prop :=
  (∀ format : List Char, format.length < 128 → strftimeTm format = format)
theorem strftimeWrappers_1 : StrftimeWrappers_1 := by
  have h := strftimeWrappers
  exact h.1

def StrftimeWrappers_2 : Prop :=
  (∀ lt f t, -9223372036854775808 ≤ t → t ≤ 9223372036854775807 →
      strftimeReal lt f t = .ok (strftimeTm (f (lt t))))
theorem strftimeWrappers_2 : StrftimeWrappers_2 := by
  have h := strftimeWrappers
  exact h.2.1

def StrftimeWrappers_3 : Prop :=
  (∀ lt f t, strftime1 lt f t = strftimeReal lt f t)
theorem strftimeWrappers_3 : StrftimeWrappers_3 := by
  have h := strftimeWrappers
  exact h.2.2

def StrptimeCorrect_1 : Prop :=
  (∀ c, strptime c = if (c tmStruct0).1 then .ok (c tmStruct0).2 else argErr "invalid arguments")
theorem strptimeCorrect_1 : StrptimeCorrect_1 := by
  have h := strptimeCorrect
  exact h.1

def StrptimeCorrect_2 : Prop :=
  (∀ c, strptime1 c = strptime c)
theorem strptimeCorrect_2 : StrptimeCorrect_2 := by
  have h := strptimeCorrect
  exact h.2.1

def StrptimeCorrect_3 : Prop :=
  (∀ mk tm, timeTm mk tm = mk tm)
theorem strptimeCorrect_3 : StrptimeCorrect_3 := by
  have h := strptimeCorrect
  exact h.2.2.1

def StrptimeCorrect_4 : Prop :=
  (∀ c, timeNow c = c ())
theorem strptimeCorrect_4 : StrptimeCorrect_4 := by
  have h := strptimeCorrect
  exact h.2.2.2

def ProcessQueriesCorrect_1 : Prop :=
  (∀ c, getpid c = c ())
theorem processQueriesCorrect_1 : ProcessQueriesCorrect_1 := by
  have h := processQueriesCorrect
  exact h.1

def ProcessQueriesCorrect_2 : Prop :=
  (∀ c, gethostname c = if (c 256).1 = 0 then .ok ((c 256).2.takeWhile (· != 0))
      else .error (.systemError "gethostname"))
theorem processQueriesCorrect_2 : ProcessQueriesCorrect_2 := by
  have h := processQueriesCorrect
  exact h.2.1

def ProcessQueriesCorrect_3 : Prop :=
  (∀ s, errnoGet s = s)
theorem processQueriesCorrect_3 : ProcessQueriesCorrect_3 := by
  have h := processQueriesCorrect
  exact h.2.2.1

def ProcessQueriesCorrect_4 : Prop :=
  (∀ e, errnoSet e = toInt .i32 e)
theorem processQueriesCorrect_4 : ProcessQueriesCorrect_4 := by
  have h := processQueriesCorrect
  exact h.2.2.2.1

def ProcessQueriesCorrect_5 : Prop :=
  (∀ c e, -2147483648 ≤ e → e ≤ 2147483647 → strerror c e = .ok (c e))
theorem processQueriesCorrect_5 : ProcessQueriesCorrect_5 := by
  have h := processQueriesCorrect
  exact h.2.2.2.2.1

def ProcessQueriesCorrect_6 : Prop :=
  (∀ c e, strerror0 c e = strerror c e)
theorem processQueriesCorrect_6 : ProcessQueriesCorrect_6 := by
  have h := processQueriesCorrect
  exact h.2.2.2.2.2

def MemoryCorrect_1 : Prop :=
  (∀ c p, free c p = c p ∧ freeCstring c p = c p ∧ freeCwstring c p = c p)
theorem memoryCorrect_1 : MemoryCorrect_1 := by
  have h := memoryCorrect
  exact h.1

def MemoryCorrect_2 : Prop :=
  (∀ c size, 0 ≤ size → size ≤ 18446744073709551615 → malloc c size = .ok (c size))
theorem memoryCorrect_2 : MemoryCorrect_2 := by
  have h := memoryCorrect
  exact h.2.1

def MemoryCorrect_3 : Prop :=
  (∀ c size, size < 0 → malloc c size = .error (.jl (.inexactError "UInt64")))
theorem memoryCorrect_3 : MemoryCorrect_3 := by
  have h := memoryCorrect
  exact h.2.2.1

def MemoryCorrect_4 : Prop :=
  (∀ c p size, 0 ≤ size → size ≤ 18446744073709551615 → realloc c p size = .ok (c p size))
theorem memoryCorrect_4 : MemoryCorrect_4 := by
  have h := memoryCorrect
  exact h.2.2.2.1

def MemoryCorrect_5 : Prop :=
  (∀ c a b, 0 ≤ a → a ≤ 18446744073709551615 → 0 ≤ b → b ≤ 18446744073709551615 →
      calloc c a b = .ok (c a b))
theorem memoryCorrect_5 : MemoryCorrect_5 := by
  have h := memoryCorrect
  exact h.2.2.2.2

def RandomCorrect_1 : Prop :=
  (∀ u len, getrandom u len = if (u len).1 < 0 then .error (.uvError "getrandom") else .ok (u len).2)
theorem randomCorrect_1 : RandomCorrect_1 := by
  have h := randomCorrect
  exact h.1

def RandomCorrect_2 : Prop :=
  (∀ x, rand x < 2 ^ 32 ∧ randU32 x = rand x)
theorem randomCorrect_2 : RandomCorrect_2 := by
  have h := randomCorrect
  exact h.2.1

def RandomCorrect_3 : Prop :=
  (∀ x, (randF64 x).1 < (randF64 x).2)
theorem randomCorrect_3 : RandomCorrect_3 := by
  have h := randomCorrect
  exact h.2.2.1

def RandomCorrect_4 : Prop :=
  (∀ s, 0 ≤ srand s ∧ srand s < 2 ^ 64 ∧ (srand s - s) % 2 ^ 64 = 0)
theorem randomCorrect_4 : RandomCorrect_4 := by
  have h := randomCorrect
  exact h.2.2.2

def UsersCorrect_1 : Prop :=
  (∀ c path mode, 0 ≤ mode → mode ≤ 4294967295 →
      mkfifo c path mode = if c path mode = -1 then .error (.systemError "mkfifo") else .ok path) ∧
  cpasswd0.username = none ∧
  cpasswd0.uid = 2 ^ 64 - 1 ∧
  cgroup0.mem = none
theorem usersCorrect_1 : UsersCorrect_1 := by
  have h := usersCorrect
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

def UsersCorrect_2 : Prop :=
  (∀ c, getpw c = if (c cpasswd0).1 < 0 then .error (.uvError "getpw") else .ok (passwdOf (c cpasswd0).2))
theorem usersCorrect_2 : UsersCorrect_2 := by
  have h := usersCorrect
  exact h.2.2.2.2.1

def UsersCorrect_3 : Prop :=
  (∀ pd : Cpasswd, pd.username = none → (passwdOf pd).username = [])
theorem usersCorrect_3 : UsersCorrect_3 := by
  have h := usersCorrect
  exact h.2.2.2.2.2.1

def UsersCorrect_4 : Prop :=
  (∀ c uid, (c cpasswd0 uid).1 ≠ 0 → getpwuid c uid false = .ok none)
theorem usersCorrect_4 : UsersCorrect_4 := by
  have h := usersCorrect
  exact h.2.2.2.2.2.2.1

def UsersCorrect_5 : Prop :=
  (∀ c uid, (c cpasswd0 uid).1 = 0 → getpwuid c uid true = .ok (some (passwdOf (c cpasswd0 uid).2)))
theorem usersCorrect_5 : UsersCorrect_5 := by
  have h := usersCorrect
  exact h.2.2.2.2.2.2.2.1

def UsersCorrect_6 : Prop :=
  (∀ c gid, (c cgroup0 gid).1 < 0 → getgrgid c gid true = .error (.uvError "getgrgid"))
theorem usersCorrect_6 : UsersCorrect_6 := by
  have h := usersCorrect
  exact h.2.2.2.2.2.2.2.2.1

def UsersCorrect_7 : Prop :=
  (∀ c gid, (c cgroup0 gid).1 = 0 → (c cgroup0 gid).2.mem = none →
      getgrgid c gid false = .ok (some ⟨cstrOrEmpty (c cgroup0 gid).2.groupname, (c cgroup0 gid).2.gid, []⟩))
theorem usersCorrect_7 : UsersCorrect_7 := by
  have h := usersCorrect
  exact h.2.2.2.2.2.2.2.2.2.1

def UsersCorrect_8 : Prop :=
  (∀ c, getuid c = c () ∧ geteuid c = c () ∧ getegid c = c ())
theorem usersCorrect_8 : UsersCorrect_8 := by
  have h := usersCorrect
  exact h.2.2.2.2.2.2.2.2.2.2

end JuliaLean.IOCov.Libc
