import JuliaLean.BootCov.Misc
import JuliaLean.BootCov.IntConvProofs

/-!
Properties of the remaining `base/boot.jl` and `base/essentials.jl` methods.
-/

namespace JuliaLean.BootCov.Misc

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

theorem printN_append (io : CoreIO) (ss : PrintArg → List Nat) :
    ∀ (xs : List PrintArg) (s : Out),
      printN io ss xs s = emit io (xs.flatMap (printBytes ss)) s := by
  intro xs
  induction xs with
  | nil => intro s; cases io <;> simp [printN, emit]
  | cons x xs ih =>
    intro s
    rw [printN, ih]
    cases io <;> cases x <;>
      simp [print1, emit, printBytes, writeString, unsafeWrite, coreShow, List.append_assoc]

/-- The stand-alone `Core` printing (`base/boot.jl:970-1006`): `write` returns the number
of bytes and appends them; `print(io, xs...)` appends each argument's bytes in order
(characters and strings verbatim, other values through `jl_static_show`); `println`
appends a newline after them; output to one stream leaves the other unchanged; and the
one-argument forms print to `Core.stdout`. -/
def CorePrinting : Prop :=
  coreSTDOUT = .stdout ∧ coreSTDERR = .stderr ∧
  (∀ h, ioPointer h .stdout = h.1 ∧ ioPointer h .stderr = h.2) ∧
  (∀ io bs nb s, (unsafeWrite io bs nb s).1 = nb) ∧
  (∀ bs s, (writeString .stdout bs s) = (bs.length, { s with out := s.out ++ bs })) ∧
  (∀ x s, writeByte .stderr x s = (1, { s with err := s.err ++ [x] })) ∧
  (∀ ss xs s, printlnN .stdout ss xs s =
    { s with out := s.out ++ xs.flatMap (printBytes ss) ++ [10] }) ∧
  (∀ ss xs s, (printlnN .stderr ss xs s).out = s.out) ∧
  (∀ ss xs s, print0 ss xs s = printN .stdout ss xs s ∧
    printlnStdout ss xs s = printlnN .stdout ss xs s) ∧
  (∀ ss x s, show0 ss x s = { s with out := s.out ++ ss x })

theorem corePrinting : CorePrinting := by
  refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, ?_, fun _ _ => rfl, ?_, ?_,
    fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  · intro bs s; simp [writeString, unsafeWrite, emit]
  · intro ss xs s
    simp [printlnN, println0, writeByte, printN_append, emit, List.append_assoc]
  · intro ss xs s
    simp [printlnN, println0, writeByte, printN_append, emit]

/-- The `Core` conversions (`base/boot.jl:381-384`): `convert(Any, x)`, `convert(T, x::T)`
and `unsafe_convert(T, x::T)` return their argument, `Core.cconvert(T, x)` is
`convert(T, x)`; and `Union{}(a...)` and `kwcall(kw, Union{}, a...)` (lines 398-399)
throw `ArgumentError`. -/
def IdentityConversionsBoot : Prop :=
  (∀ {α : Type} (x : α), convertSame x = x ∧ unsafeConvertSame x = x) ∧
  (∀ {α β : Type} (f : α → β) x, coreCconvert f x = f x) ∧
  (∀ {α : Type} (a : List α), ∃ m, unionBottomCtor a = .error (.argument m)) ∧
  (∀ {α : Type} (k : α) (a : List α), kwcallUnionBottom k a = unionBottomCtor a)

theorem identityConversionsBoot : IdentityConversionsBoot :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => ⟨_, rfl⟩, fun _ _ => rfl⟩

/-- The `Base` identity conversions (`base/essentials.jl:474-480`, 652, 739-746) return
their argument; `cconvert(T, x)` converts only when `x` is not already a `T`, and defers
pointers; pointer `unsafe_convert` keeps the address and string `unsafe_convert` yields the
data address; converting to `Union{}` throws `ArgumentError`. -/
def IdentityConversionsBase : Prop :=
  (∀ {α : Type} (x : α), convertSame x = x ∧ unsafeConvertSame x = x ∧ cconvertPtr x = x) ∧
  (∀ {α : Type} (isT : α → Bool) (conv : α → R α) x, isT x = true → cconvert isT conv x = .ok x) ∧
  (∀ {α : Type} (isT : α → Bool) (conv : α → R α) x, isT x = false → cconvert isT conv x = conv x) ∧
  (∀ p : Ptr, (unsafeConvertPtr p).addr = p.addr) ∧
  (∀ a, (unsafeConvertString a).addr = a) ∧
  (∀ {α : Type} (a : List α), (∃ m, convertUnionBottom a = .error (.argument m)) ∧
    cconvertUnionBottom a = convertUnionBottom a)

theorem identityConversionsBase : IdentityConversionsBase := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, fun _ => rfl, fun _ => rfl,
    fun _ => ⟨⟨_, rfl⟩, rfl⟩⟩
  · intro α isT conv x h; simp [cconvert, h]
  · intro α isT conv x h; simp [cconvert, h]

theorem cvtFrom_all_isa {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) :
    ∀ (x : List α) (n : Nat), (∀ i (h : i < x.length), isa (n + i) x[i] = true) →
      cvtFrom isa conv n x = .ok x := by
  intro x
  induction x with
  | nil => intro n _; rfl
  | cons a x ih =>
    intro n h
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hr := ih (n + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show n + 1 + i = n + (i + 1) by omega]
      exact this)
    simp [cvtFrom, h0, hr, bind, Except.bind, pure, Except.pure]

theorem bind_ok {α β : Type} {m : R α} {k : α → R β} {y : β} (h : (m >>= k) = .ok y) :
    ∃ b, m = .ok b ∧ k b = .ok y := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok b => exact ⟨b, rfl, h⟩

theorem cvtFrom_length {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) :
    ∀ (x : List α) (n : Nat) (y : List α), cvtFrom isa conv n x = .ok y → y.length = x.length := by
  intro x
  induction x with
  | nil => intro n y h; simp [cvtFrom] at h; cases h; rfl
  | cons a x ih =>
    intro n y h
    rw [cvtFrom.eq_2] at h
    split at h <;>
    · obtain ⟨b, -, h⟩ := bind_ok h
      dsimp only at h
      obtain ⟨ys, hys, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [ih (n + 1) ys hys]

/-- Tuple helpers (`base/essentials.jl:521-667`): `tail(x)` drops the first element and
throws `ArgumentError` on `()`; `argtail` drops its first argument; `convert(T, x)` for
a tuple throws `MethodError` when no conversion can produce a `T`, returns `x` itself when
every element already has its field type, keeps the length, and converts each other
element with `convert(fieldtype(T, n), x[n])`. -/
def TupleHelpers : Prop :=
  (∀ {α : Type} (a : α) (xs : List α), tail (a :: xs) = .ok xs ∧ argtail (a :: xs) = .ok xs) ∧
  (∀ {α : Type}, ∃ m, tail ([] : List α) = .error (.argument m)) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x : List α),
    convertTuple false isa conv x = .error (.method "convert")) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x : List α),
    (∀ i (h : i < x.length), isa (i + 1) x[i] = true) → convertTuple true isa conv x = .ok x) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x y : List α),
    convertTuple true isa conv x = .ok y → y.length = x.length) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x : List α) (n : Nat)
    (h : n < x.length), cvt1 isa conv x (n + 1) =
      if isa (n + 1) x[n] then .ok x[n] else conv (n + 1) x[n])

theorem tupleHelpers : TupleHelpers := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, ⟨_, rfl⟩, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro α isa conv x h
    simp only [convertTuple, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact cvtFrom_all_isa isa conv x 1 (fun i hi => by rw [Nat.add_comm]; exact h i hi)
  · intro α isa conv x y h
    simp only [convertTuple, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact cvtFrom_length isa conv x 1 y h
  · intro α isa conv x n h
    simp [cvt1, h]

/-- Small functions of `base/essentials.jl`: the compiler barriers and `values` return their
argument; every `throw_boundserror` form throws `BoundsError(A, indices)` with the indices
as a tuple; `GlobalRef`s are equal exactly when module and name are; `oftype` converts only
when needed; `unsigned`/`signed` reinterpret the 64-bit pattern and invert each other;
`reinterpret` bit-casts primitive types; `ifelse` selects; `isempty` uses `isdone` when it
answers and otherwise whether `iterate` returns `nothing`; `Int` `+`/`-` wrap; `!` negates;
`ismissing` tests for `missing`; `isdone` defaults to `missing`; and `_resolve_in_world`
throws `InexactError` for a negative world. -/
def SmallFunctions : Prop :=
  (∀ {α : Type} (x : α), blackbox x = x ∧ inferencebarrier x = x ∧ values x = x) ∧
  (∀ A I, throwBoundserror A I = (.error .bounds, .obj "BoundsError" [some A, some (.tuple I)])) ∧
  (∀ A, throwBoundserror1 A = throwBoundserror A []) ∧
  (∀ A i1 i2 I, throwBoundserror3 A i1 i2 I = throwBoundserror A (i1 :: i2 :: I)) ∧
  (∀ A I, throwBoundserrorIndices A I = throwBoundserror A I) ∧
  (∀ A I, throwBoundserror2 A I = (.error .bounds, .obj "BoundsError" [some A, some I])) ∧
  (∀ a b : String × String, globalRefEq a b = true ↔ a = b) ∧
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y, isa y = true → oftype isa conv y = .ok y) ∧
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y r, isa y = false → conv y = .ok r →
    oftype isa conv y = if isa r then .ok r else .error (.typeError "typeassert")) ∧
  (∀ x : JInt64, signedUInt (unsignedInt x) = x) ∧
  (∀ x : JInt .u64, unsignedInt (signedUInt x) = x) ∧
  (∀ x : JInt64, (unsignedInt x).val = x.val % 2 ^ 64) ∧
  (∀ {α β : Type} (bc : α → β) (full : α → R β) x, reinterpret true bc full x = .ok (bc x) ∧
    reinterpret false bc full x = full x) ∧
  (∀ {α : Type} (f : α → Nat) x, sizeof f x = f x) ∧
  (∀ {α : Type} (x y : α), ifelse true x y = x ∧ ifelse false x y = y) ∧
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s d, isdone s = some d →
    isempty isdone it s = d) ∧
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s, isdone s = none →
    isempty isdone it s = (it s).isNone) ∧
  (∀ x y : JInt64, (addInt x y).val = wrapInt .i64 (x.val + y.val) ∧
    (subInt x y).val = wrapInt .i64 (x.val - y.val)) ∧
  (∀ b, notBool b = !b) ∧
  (∀ x, ismissing x = true ↔ x = none) ∧
  (∀ {α : Type} (x : α), isdoneDefault x = none) ∧
  (∀ {τ : Type} (hm : τ → Bool) T, isiterable hm T = hm T) ∧
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr, w.val < 0 →
    resolveInWorld g (.int .i64 w) gr = .error (.inexact "convert" "UInt64")) ∧
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr (h : 0 ≤ w.val),
    resolveInWorld g (.int .i64 w) gr = g ⟨w.val, by
      have := w.property; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at this ⊢; omega⟩
      gr.1 gr.2)

theorem i64_val_bounds (x : JInt64) : -(2:Int) ^ 63 ≤ x.val ∧ x.val < 2 ^ 63 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem u64_val_bounds (x : JInt .u64) : 0 ≤ x.val ∧ x.val < 2 ^ 64 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem smallFunctions : SmallFunctions := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_, fun _ => rfl,
    fun _ _ => rfl, ?_, ?_⟩
  · intro a b
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp [globalRefEq]
  · intro α isa conv y h; simp [oftype, h]
  · intro α isa conv y r h hr; simp [oftype, h, hr, bind, Except.bind]
  · intro x
    apply Subtype.ext
    have hb := i64_val_bounds x
    simp only [signedUInt, unsignedInt, bitcastInt, JInt.wrap]
    simp [wrapInt, IntTy.signed, IntTy.bits]
    omega
  · intro x
    apply Subtype.ext
    have hb := u64_val_bounds x
    simp only [signedUInt, unsignedInt, bitcastInt, JInt.wrap]
    simp [wrapInt, IntTy.signed, IntTy.bits]
    omega
  · intro x
    simp [unsignedInt, bitcastInt, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
  · intro σ α isdone it s d h; simp [isempty, h]
  · intro σ α isdone it s h; simp [isempty, h]
  · intro x; cases x <;> simp [ismissing]
  · intro g w gr h
    have ht : wrapInt IntTy.i64.toSigned w.val < 0 := by
      have hb := i64_val_bounds w
      simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.toSigned]
      omega
    have herr : ctor .u64 (.int .i64 w) = .error (.inexact "convert" "UInt64") := by
      simp only [ctor, toUInt64, bind_checkSignBit, ht, ↓reduceIte, throwInexact]
      try rfl
    simp [resolveInWorld, herr, bind, Except.bind]
  · intro g w gr h
    have hb := i64_val_bounds w
    have hok : ctor .u64 (.int .i64 w) = .ok ⟨w.val, by
        have := w.property; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at this ⊢; omega⟩ := by
      simp only [ctor, toUInt64, bind_checkSignBit]
      have ht : ¬ wrapInt IntTy.i64.toSigned w.val < 0 := by
        simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.toSigned]
        omega
      simp only [ht, ↓reduceIte, pure, Except.pure, bitcastInt]
      congr 1
      apply Subtype.ext
      simp [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
      omega
    simp [resolveInWorld, hok, bind, Except.bind]

/-- `blackbox(x)`, `inferencebarrier(x)` and `values(itr)` (`base/essentials.jl:9`, 1201, 1253) return their argument unchanged. -/
def Barriers : Prop :=
  (∀ {α : Type} (x : α), blackbox x = x ∧ inferencebarrier x = x ∧ values x = x)

theorem barriers : Barriers := smallFunctions.1

/-- Every `throw_boundserror` and `_throw_boundserror_indices` method (`base/essentials.jl:15-19`) throws `BoundsError(A, I)`, with the indices collected into a tuple by the splatting forms. -/
def ThrowBoundserrorForms : Prop :=
  (∀ A I, throwBoundserror A I = (.error .bounds, .obj "BoundsError" [some A, some (.tuple I)])) ∧
  (∀ A, throwBoundserror1 A = throwBoundserror A []) ∧
  (∀ A i1 i2 I, throwBoundserror3 A i1 i2 I = throwBoundserror A (i1 :: i2 :: I)) ∧
  (∀ A I, throwBoundserrorIndices A I = throwBoundserror A I) ∧
  (∀ A I, throwBoundserror2 A I = (.error .bounds, .obj "BoundsError" [some A, some I]))

theorem throwBoundserrorForms : ThrowBoundserrorForms := ⟨smallFunctions.2.1, smallFunctions.2.2.1, smallFunctions.2.2.2.1, smallFunctions.2.2.2.2.1, smallFunctions.2.2.2.2.2.1⟩

/-- `==(a::GlobalRef, b::GlobalRef) = a.mod === b.mod && a.name === b.name` (`base/essentials.jl:23`) holds exactly for equal module and name. -/
def GlobalRefEq : Prop :=
  (∀ a b : String × String, globalRefEq a b = true ↔ a = b)

theorem globalRefEq_spec : GlobalRefEq := smallFunctions.2.2.2.2.2.2.1

/-- `oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)`
(`base/essentials.jl:718`): `y` itself when it already has the type, otherwise the result of
the (arbitrary, user-extensible) `convert` method, which the typeassert requires to have the
type. -/
def OftypeSpec : Prop :=
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y, isa y = true → oftype isa conv y = .ok y) ∧
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y r, isa y = false → conv y = .ok r →
    oftype isa conv y = if isa r then .ok r else .error (.typeError "typeassert"))

theorem oftypeSpec : OftypeSpec := ⟨smallFunctions.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.1⟩

/-- `unsigned(x::Int) = reinterpret(UInt, x)` and `signed(x::UInt) = reinterpret(Int, x)`
(`base/essentials.jl:720-721`) reinterpret the 64-bit pattern: they invert each other and `unsigned(x)` is `x mod 2^64`. -/
def SignedUnsignedInt : Prop :=
  (∀ x : JInt64, signedUInt (unsignedInt x) = x) ∧
  (∀ x : JInt .u64, unsignedInt (signedUInt x) = x) ∧
  (∀ x : JInt64, (unsignedInt x).val = x.val % 2 ^ 64)

theorem signedUnsignedInt : SignedUnsignedInt := ⟨smallFunctions.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- `reinterpret(Out, x)` (`base/essentials.jl:787-794`) bit-casts when both types are primitive and otherwise defers to `_reinterpret`. -/
def ReinterpretSpec : Prop :=
  (∀ {α β : Type} (bc : α → β) (full : α → R β) x, reinterpret true bc full x = .ok (bc x) ∧
    reinterpret false bc full x = full x)

theorem reinterpretSpec : ReinterpretSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `sizeof(x) = Core.sizeof(x)` (`base/essentials.jl:841`) is the runtime size. -/
def SizeofSpec : Prop :=
  (∀ {α : Type} (f : α → Nat) x, sizeof f x = f x)

theorem sizeofSpec : SizeofSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `ifelse(c, x, y)` (`base/essentials.jl:884`) returns `x` when `c` is true and `y` otherwise. -/
def IfelseSpec : Prop :=
  (∀ {α : Type} (x y : α), ifelse true x y = x ∧ ifelse false x y = y)

theorem ifelseSpec : IfelseSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `isempty(itr)` (`base/essentials.jl:1225-1229`) answers with `isdone(itr)` when that is not `missing`, and otherwise whether `iterate(itr)` returns `nothing`. -/
def IsemptySpec : Prop :=
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s d, isdone s = some d →
    isempty isdone it s = d) ∧
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s, isdone s = none →
    isempty isdone it s = (it s).isNone)

theorem isemptySpec : IsemptySpec := ⟨smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The bootstrap `(+)(x::Int, y::Int)` and `(-)(x::Int, y::Int)` (`base/essentials.jl:1257-1258`) wrap modulo `2^64`. -/
def IntAddSub : Prop :=
  (∀ x y : JInt64, (addInt x y).val = wrapInt .i64 (x.val + y.val) ∧
    (subInt x y).val = wrapInt .i64 (x.val - y.val))

theorem intAddSub : IntAddSub := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `!(x::Bool) = not_int(x)` (`base/essentials.jl:1284`) is Boolean negation. -/
def NotBool : Prop :=
  (∀ b, notBool b = !b)

theorem notBool_spec : NotBool := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `ismissing(x) = x === missing` (`base/essentials.jl:1532`). -/
def IsmissingSpec : Prop :=
  (∀ x, ismissing x = true ↔ x = none)

theorem ismissingSpec : IsmissingSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The fallback `isdone(itr, state...) = missing` (`base/essentials.jl:1591`). -/
def IsdoneDefault : Prop :=
  (∀ {α : Type} (x : α), isdoneDefault x = none)

theorem isdoneDefault_spec : IsdoneDefault := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `isiterable(T) = hasmethod(iterate, Tuple{T})` (`base/essentials.jl:1608-1610`). -/
def IsiterableSpec : Prop :=
  (∀ {τ : Type} (hm : τ → Bool) T, isiterable hm T = hm T)

theorem isiterableSpec : IsiterableSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `_resolve_in_world(world, gr) = getglobal(gr.mod, gr.name)` in world `UInt(world)` (`base/essentials.jl:1662-1663`): a negative world throws `InexactError`, any other world reads the binding in that world. -/
def ResolveInWorld : Prop :=
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr, w.val < 0 →
    resolveInWorld g (.int .i64 w) gr = .error (.inexact "convert" "UInt64")) ∧
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr (h : 0 ≤ w.val),
    resolveInWorld g (.int .i64 w) gr = g ⟨w.val, by
      have := w.property; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at this ⊢; omega⟩
      gr.1 gr.2)

theorem resolveInWorld_spec : ResolveInWorld := ⟨smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The `Pairs` constructors (`base/essentials.jl:505-513`): the four-parameter inner
constructor converts only arguments that do not already have the declared types; the outer
constructors choose `V = eltype(A)` and `K = eltype(I)`, or `keytype(A)` when `I` is
`Nothing`; `pairs(NamedTuple)` has `Symbol` keys and a `Nothing` iterator; `Colon()` is
the field-less singleton and `show(io, ::Colon)` prints the type name followed by `()`;
`Val(x)` is `Val{x}()`, which carries `x` in its type (`base/essentials.jl:1160-1193`). -/
def PairsAndColon : Prop :=
  (∀ {α : Type} (isA isI : α → Bool) (cA cI : α → R α) d i, isA d = true → isI i = true →
    pairsKVIA isA isI cA cI d i = .ok (d, i)) ∧
  (∀ {α : Type} (isA isI : α → Bool) (cA cI : α → R α) d i d', isA d = false → isI i = true →
    cA d = .ok d' → pairsKVIA isA isI cA cI d i = .ok (d', i)) ∧
  (∀ K V I A, pairsKV K V I A = (K, V, I, A)) ∧
  (∀ (elt : String → String) K I A, pairsK elt K I A = (K, elt A, I, A)) ∧
  (∀ (elt kt : String → String) A, pairs0 elt kt "Nothing" A = (kt A, elt A, "Nothing", A)) ∧
  (∀ (elt kt : String → String) I A, I ≠ "Nothing" → pairs0 elt kt I A = (elt I, elt A, I, A)) ∧
  pairsNamedTupleType = ("Symbol", "Nothing") ∧
  showColon "Colon" = "Colon()" ∧ colonCtor = .obj "Colon" [] ∧
  (∀ x, valCtor x = valT x ∧ (valT x).1 = x)

theorem pairsAndColon : PairsAndColon := by
  refine ⟨?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl⟩⟩
  · intro α isA isI cA cI d i h1 h2; simp [pairsKVIA, h1, h2, bind, Except.bind, pure, Except.pure]
  · intro α isA isI cA cI d i d' h1 h2 h3
    simp [pairsKVIA, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  · intro elt kt A; simp [pairs0]
  · intro elt kt I A h; simp [pairs0, h]

/-- The `Core` hooks and shims (`base/boot.jl:1227-1281`): `struct_name_shim` returns the
type under construction exactly when `x === mod` and otherwise reads `getfield(x, name)`;
each `_set...!` installs its hook, returns it and leaves the other hooks alone; and
`_hasmethod(tt)` is true exactly when method lookup in the current world finds a method. -/
def CoreHooks : Prop :=
  (∀ {α : Type} (gf : α → String → R α) x n t, structNameShim gf true x n t = .ok t) ∧
  (∀ {α : Type} (gf : α → String → R α) x n t, structNameShim gf false x n t = gf x n) ∧
  (∀ {α : Type} (h : Hooks α) p, setparser h p = (p, ⟨p, h.lower, h.toplevelEval⟩)) ∧
  (∀ {α : Type} (h : Hooks α) l, setlowerer h l = (l, ⟨h.parse, l, h.toplevelEval⟩)) ∧
  (∀ {α : Type} (h : Hooks α) f, setToplevelEval h f = (f, ⟨h.parse, h.lower, f⟩)) ∧
  (∀ {τ μ : Type} (lookup : τ → Nat → Option μ) w tt,
    hasmethod lookup w tt = true ↔ ∃ m, lookup tt w = some m)

theorem coreHooks : CoreHooks := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, ?_⟩
  · intro τ μ lookup w tt
    simp only [hasmethod]
    cases lookup tt w <;> simp

end JuliaLean.BootCov.Misc
