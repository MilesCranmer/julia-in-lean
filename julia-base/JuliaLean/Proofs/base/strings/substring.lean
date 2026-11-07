import JuliaLean.base.strings.substring
import JuliaLean.Registry.Types

/-!
# Properties of `base/strings/substring.jl`

The statements use the source-mirrored methods and documented laws of external string and memory interfaces.
-/

namespace JuliaLean.Proofs.base.strings.substring

open _root_.JuliaLean _root_.JuliaLean.base.strings.substring _root_.JuliaLean.Registry

abbrev Index := JuliaLean.base.strings.substring.Index

private instance {E A : Type} [DecidableEq E] [DecidableEq A] : DecidableEq (Except E A)
  | .error a, .error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun h' => h (Except.error.inj h'))
  | .ok a, .ok b =>
    if h : a = b then isTrue (congrArg Except.ok h)
    else isFalse (fun h' => h (Except.ok.inj h'))
  | .error _, .ok _ => isFalse nofun
  | .ok _, .error _ => isFalse nofun

@[simp] private theorem pure_ok {E A : Type} (a : A) :
    (pure a : Except E A) = .ok a := rfl

private theorem ofNat_add (n m : Nat) :
    Int.ofNat (n + m) = Int.ofNat n + Int.ofNat m := rfl

@[simp] private theorem ofNat_one : Int.ofNat 1 = 1 := rfl

@[simp] private theorem bind_ok {E A B : Type} (a : A) (f : A → Except E B) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem bind_error {E A B : Type} (e : E) (f : A → Except E B) :
    (Except.error e >>= f) = .error e := rfl
@[simp] private theorem throw_error {E A : Type} (e : E) :
    (throw e : Except E A) = .error e := rfl

private theorem zero_val : zero.val = 0 := by decide
private theorem one_val : one.val = 1 := by decide

private theorem add_val (a b : Index)
    (h : IntTy.min .i64 ≤ a.val + b.val ∧ a.val + b.val ≤ IntTy.max .i64) :
    (a + b).val = a.val + b.val := by
  exact wrapInt_of_inRange .i64 _ h

private theorem sub_val (a b : Index)
    (h : IntTy.min .i64 ≤ a.val - b.val ∧ a.val - b.val ≤ IntTy.max .i64) :
    (a - b).val = a.val - b.val := by
  exact wrapInt_of_inRange .i64 _ h

private theorem sub_one_val (i : Index) (hi : 1 ≤ i.val) :
    (i - one).val = i.val - 1 := by
  have hb := i.property
  have ho := one_val
  rw [sub_val]
  · omega
  · change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at hb
    omega

private theorem available_val (n i : Index) (hn : 0 ≤ n.val) (hi : 1 ≤ i.val) :
    (n - i + one).val = n.val - i.val + 1 := by
  have hb := n.property
  have ib := i.property
  have ho := one_val
  have hs : (n - i).val = n.val - i.val := sub_val n i (by
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hb
    change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at ib
    omega)
  rw [add_val, hs, ho]
  change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hb
  change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at ib
  rw [hs, ho]
  omega

/-- Every successful raw byte view stays inside its parent string. -/
def RawSubstringWithinParent : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (s : S)
    (first count : Index) (ss : SubString S),
    0 ≤ (ops.ncodeunits s).val →
    rawSubstring ops s first count = .ok ss →
      ss.string = s ∧ 0 ≤ ss.offset.val ∧ 0 ≤ ss.ncodeunits.val ∧
        ss.offset.val + ss.ncodeunits.val ≤ (ops.ncodeunits s).val

/-- An empty character range retains the requested insertion position. -/
def EmptySubstringOffset : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (s : S)
    (i j : Index) (ss : SubString S),
    typedSubString ops s i j = .ok ss → j.val < i.val → ss.offset.val = i.val - 1

/-- The parent position of every in-view index lies in the parent's code-unit span. -/
def SubstringIndexArithmetic : Prop :=
  ∀ (parentLength offset count index : Int),
    0 ≤ offset → 0 ≤ count → offset + count ≤ parentLength →
    1 ≤ index → index ≤ count →
      1 ≤ offset + index ∧ offset + index ≤ parentLength

/-- Returned parent indices use mathematical, non-wrapping coordinates. -/
def ParentIndices : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (ss : SubString S)
    (starts : S → List Index) (indices : IndexRange),
    0 ≤ ss.offset.val → 0 ≤ ss.ncodeunits.val →
    ss.offset.val + ss.ncodeunits.val < IntTy.max .i64 →
    (∀ i last, ops.thisindParent ss.string i = .ok last →
      0 ≤ last.val ∧ last.val ≤ i.val ∧ ((last.val = 0 ∧ i.val = 0) ∨ last ∈ starts ss.string)) →
    parentindicesSubString ops ss = .ok indices →
      indices.first.val = ss.offset.val + 1 ∧
      0 ≤ indices.last.val ∧
      indices.last.val ≤ ss.offset.val + ss.ncodeunits.val ∧
      ops.thisindParent ss.string (ss.offset + ss.ncodeunits) = .ok indices.last ∧
      (indices.last.val = 0 ∨ indices.last ∈ starts ss.string) ∧
      (0 < ss.ncodeunits.val → indices.last ∈ starts ss.string)

private def concreteOps : SubStringOps
    JuliaLean.base.strings.basic.StringData UInt32 Unit JlError where
  ncodeunits := JuliaLean.base.strings.basic.stringDataOps.ncodeunits
  codeunitType := fun _ => ()
  length := JuliaLean.base.strings.basic.lengthInt JuliaLean.base.strings.basic.stringDataOps
  checkboundsRange := fun _ _ _ => .ok ()
  checkboundsViewRange := fun _ _ _ => .ok ()
  isvalid := JuliaLean.base.strings.basic.stringDataOps.isvalid
  stringIndexError := fun _ _ => .methodError "StringIndexError"
  boundsError := fun _ _ _ => .boundsError
  viewBoundsError := fun _ _ _ => .boundsError
  nextind := fun s i => JuliaLean.base.strings.basic.stringDataOps.nextind s i one
  firstindex := JuliaLean.base.strings.basic.firstindexString
  thisindParent := JuliaLean.base.strings.basic.stringDataOps.thisind
  isasciiCodeunits := fun units =>
    .ok (((units.s.string.bytes.drop units.s.offset.val.toNat).take units.s.ncodeunits.val.toNat).all
      (fun b => decide (b.toNat < 128)))
  sizeof := JuliaLean.base.strings.basic.stringDataOps.ncodeunits
private def checkedView (ss : SubString JuliaLean.base.strings.basic.StringData) (i : Index) :
    Except JlError Unit :=
  JuliaLean.base.strings.basic.checkboundsThrow
    (.ok (JuliaLean.base.strings.basic.checkboundsScalar ncodeunitsSubString
      (fun i => decide (1 ≤ i.val)) (fun i n => decide (i.val ≤ n.val)) ss i))
    .boundsError
/-- The selected parent character spans are independent of SubString's iterator. -/
def SelectedParentSpans (s : JuliaLean.base.strings.basic.StringData) (first count : Index) :
    List JuliaLean.base.strings.basic.StringDataSpan :=
  (JuliaLean.base.strings.basic.stringDataSpans
    (int (Int.ofNat s.bytes.length) + one) s.starts s.chars).filter
      (fun span => decide (first.val ≤ span.first.val ∧ span.first.val < first.val + count.val))

def EndpointsAreCharacterBoundaries (s : JuliaLean.base.strings.basic.StringData)
    (first count : Index) : Prop :=
  count.val = 0 ∨
    (∃ start ∈ s.starts, start.val = first.val) ∧
    ((∃ after ∈ s.starts, after.val = first.val + count.val) ∨
      first.val + count.val = Int.ofNat s.bytes.length + 1)

/-- Complete characters agree with their parent. Truncation may cause StringIndexError,
but cannot justify a different exception or a character reaching outside the byte view. -/
def RawSubstringIterates : Prop :=
  ∀ (s : JuliaLean.base.strings.basic.StringData)
    (first count : Index) (ss : SubString JuliaLean.base.strings.basic.StringData),
    rawSubstring concreteOps s first count = .ok ss →
      let result := collectSubString
        (iterateSubString (fun i n => decide (i.val = n.val)) checkedView
          (fun off i => .ok (off + i)) JuliaLean.base.strings.basic.stringDataOps.iterateAt)
        JuliaLean.base.strings.basic.firstindexString ss
      (∃ chars, result = .ok chars ∧
        chars = (SelectedParentSpans s first count).map (·.char) ∧
        (∀ span ∈ SelectedParentSpans s first count, span.after.val ≤ first.val + count.val) ∧
        lengthSubString concreteOps ss = .ok (int (Int.ofNat chars.length))) ∨
      (¬EndpointsAreCharacterBoundaries s first count ∧
        result = .error (.methodError "StringIndexError"))

/-- Contracts of allocation, byte copying, and the String conversion callees. -/
structure RepeatInterface {S Out E I : Type} (ops : RepeatOps S Out E I) : Prop where
  empty : ops.outputSize ops.emptyString = 0
  stringCopy : ∀ s out, ops.stringFromString s = .ok out →
    ops.outputSize out = ops.sizeof (.string s)
  substringSize : ∀ ss, ops.sizeof (.substring ss) = ss.ncodeunits.val.toNat
  unsafeString : ∀ owner p n out, ops.stringCopyOps.unsafeString owner p n = .ok out →
    ops.outputSize out = n.val.toNat
  allocate : ∀ n out, ops.allocateString n = .ok out → ops.outputSize out = n
  memset : ∀ out b n result, ops.memset out b n = .ok result →
    ops.outputSize result = ops.outputSize out
  copyBlock : ∀ out s i n result, ops.copyBlock out s i n = .ok result →
    ops.outputSize result = ops.outputSize out

/-- Successful repetition has the requested byte count after the UInt conversion. -/
def RepeatSize : Prop :=
  ∀ {S Out E I : Type} (ops : RepeatOps S Out E I) (s : RepeatInput S)
    (r : I) (count : Nat) (out : Out),
    RepeatInterface ops →
    ops.toUInt r = .ok count → repeatString ops s r = .ok out →
      ops.outputSize out = count * ops.sizeof s

/-- The observable initialized prefix and capacity of an allocated byte buffer.
Only the external byte-store and integer-addition primitives are constrained here. -/
structure ByteWriterInterface {C S Sym Out E : Type}
    (ops : UnsafeStringOps C S Sym Out Index E)
    (bytes : Out → List Nat) (capacity : Out → Int) (encode : C → List Nat)
    (safe : Out → Prop := fun _ => True) : Prop where
  width : ∀ c, (ops.charCodeunits c).val = Int.ofNat (encode c).length
  widthRange : ∀ c, 1 ≤ (ops.charCodeunits c).val ∧ (ops.charCodeunits c).val ≤ 4
  encoding : ∀ c,
    let x := ops.bswap (ops.charBits c)
    encode c = [x % 256, (x / 256) % 256, (x / 256 / 256) % 256,
      (x / 256 / 256 / 256) % 256].take (ops.charCodeunits c).val.toNat
  addOffset : ∀ offset k, ops.addOffset offset k = .ok (offset + k)
  store : ∀ out offset b result,
    offset.val = Int.ofNat (bytes out).length + 1 →
    offset.val ≤ capacity out →
    ops.writeByte out offset b = .ok result →
      bytes result = bytes out ++ [b] ∧ capacity result = capacity out ∧
      (safe out → safe result)

private theorem unsafeStringChar_bytes {C S Sym Out E : Type}
    (ops : UnsafeStringOps C S Sym Out Index E) (bytes : Out → List Nat)
    (capacity : Out → Int) (encode : C → List Nat)
    {safe : Out → Prop} (laws : ByteWriterInterface ops bytes capacity encode safe)
    (out result : Out) (c : C) (offset n : Index)
    (hstart : offset.val = Int.ofNat (bytes out).length + 1)
    (hfit : Int.ofNat (bytes out).length + Int.ofNat (encode c).length ≤ capacity out)
    (hmax : capacity out < IntTy.max .i64)
    (h : unsafeStringChar ops out c offset = .ok (result, n)) :
    bytes result = bytes out ++ encode c ∧ capacity result = capacity out ∧
      n = ops.charCodeunits c ∧ (safe out → safe result) := by
  have hw := laws.width c
  have hwr := laws.widthRange c
  have he := laws.encoding c
  have hlen : 0 ≤ Int.ofNat (bytes out).length := Int.natCast_nonneg _
  let x := ops.bswap (ops.charBits c)
  change unsafeStringChar ops out c offset = .ok (result, n) at h
  simp only [unsafeStringChar] at h
  cases h0 : ops.writeByte out offset (x % 256) with
  | error e => simp [show ops.writeByte out offset (ops.bswap (ops.charBits c) % 256) = .error e from h0] at h
  | ok out0 =>
    have hb0 := laws.store out offset (x % 256) out0 hstart (by omega) h0
    simp only [show ops.writeByte out offset (ops.bswap (ops.charBits c) % 256) = .ok out0 from h0,
      bind_ok] at h
    by_cases hn1 : (ops.charCodeunits c).val = 1
    · simp [hn1] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨?_, hb0.2.1, rfl, hb0.2.2⟩
      simpa [he, hn1, x] using hb0.1
    · simp only [show ((ops.charCodeunits c).val == 1) = false from by simpa using hn1,
        Bool.false_eq_true, ite_false, laws.addOffset, bind_ok] at h
      have hv1 : (offset + one).val = offset.val + 1 := add_val _ _ (by
        have ho := one_val
        change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
        change capacity out < 9223372036854775807 at hmax
        omega)
      cases h1 : ops.writeByte out0 (offset + one) (x / 256 % 256) with
      | error e => simp [show ops.writeByte out0 (offset + one)
          (ops.bswap (ops.charBits c) / 256 % 256) = .error e from h1] at h
      | ok out1 =>
        have hb1 := laws.store out0 (offset + one) (x / 256 % 256) out1
          (by rw [hv1, hb0.1]; simp only [List.length_append, List.length_singleton,
                ofNat_add, ofNat_one]; omega)
          (by rw [hv1, hb0.2.1]; omega) h1
        simp only [show ops.writeByte out0 (offset + one)
          (ops.bswap (ops.charBits c) / 256 % 256) = .ok out1 from h1, bind_ok] at h
        by_cases hn2 : (ops.charCodeunits c).val = 2
        · simp [hn2] at h
          rcases h with ⟨rfl, rfl⟩
          refine ⟨?_, hb1.2.1.trans hb0.2.1, rfl, fun hs => hb1.2.2 (hb0.2.2 hs)⟩
          simpa [he, hn2, x, hb0.1, List.append_assoc] using hb1.1
        · simp only [show ((ops.charCodeunits c).val == 2) = false from by simpa using hn2,
            Bool.false_eq_true, ite_false] at h
          have hk2 : (int 2).val = 2 := by decide
          have hv2 : (offset + int 2).val = offset.val + 2 := by
            rw [add_val, hk2]
            change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
            change capacity out < 9223372036854775807 at hmax
            omega
          cases h2 : ops.writeByte out1 (offset + int 2) (x / 256 / 256 % 256) with
          | error e => simp [show ops.writeByte out1 (offset + int 2)
              (ops.bswap (ops.charBits c) / 256 / 256 % 256) = .error e from h2] at h
          | ok out2 =>
            have hb2 := laws.store out1 (offset + int 2) (x / 256 / 256 % 256) out2
              (by rw [hv2, hb1.1, hb0.1]; simp only [List.length_append,
                    List.length_singleton, ofNat_add, ofNat_one]; omega)
              (by rw [hv2, hb1.2.1, hb0.2.1]; omega) h2
            simp only [show ops.writeByte out1 (offset + int 2)
              (ops.bswap (ops.charBits c) / 256 / 256 % 256) = .ok out2 from h2, bind_ok] at h
            by_cases hn3 : (ops.charCodeunits c).val = 3
            · simp [hn3] at h
              rcases h with ⟨rfl, rfl⟩
              refine ⟨?_, hb2.2.1.trans (hb1.2.1.trans hb0.2.1), rfl,
                fun hs => hb2.2.2 (hb1.2.2 (hb0.2.2 hs))⟩
              simpa [he, hn3, x, hb1.1, hb0.1, List.append_assoc] using hb2.1
            · have hn4 : (ops.charCodeunits c).val = 4 := by omega
              simp only [show ((ops.charCodeunits c).val == 3) = false from by simpa using hn3,
                Bool.false_eq_true, ite_false] at h
              have hk3 : (int 3).val = 3 := by decide
              have hv3 : (offset + int 3).val = offset.val + 3 := by
                rw [add_val, hk3]
                change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
                change capacity out < 9223372036854775807 at hmax
                omega
              cases h3 : ops.writeByte out2 (offset + int 3) (x / 256 / 256 / 256 % 256) with
              | error e => simp [show ops.writeByte out2 (offset + int 3)
                  (ops.bswap (ops.charBits c) / 256 / 256 / 256 % 256) = .error e from h3] at h
              | ok out3 =>
                have hb3 := laws.store out2 (offset + int 3) (x / 256 / 256 / 256 % 256) out3
                  (by rw [hv3, hb2.1, hb1.1, hb0.1]; simp only [List.length_append,
                        List.length_singleton, ofNat_add, ofNat_one]; omega)
                  (by rw [hv3, hb2.2.1, hb1.2.1, hb0.2.1]; omega) h3
                simp only [show ops.writeByte out2 (offset + int 3)
                  (ops.bswap (ops.charBits c) / 256 / 256 / 256 % 256) = .ok out3 from h3,
                  bind_ok, pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                refine ⟨?_, hb3.2.1.trans (hb2.2.1.trans (hb1.2.1.trans hb0.2.1)), rfl,
                  fun hs => hb3.2.2 (hb2.2.2 (hb1.2.2 (hb0.2.2 hs)))⟩
                simpa [he, hn4, x, hb2.1, hb1.1, hb0.1, List.append_assoc] using hb3.1

/-- External allocation/copy contracts and the common byte-width interface. -/
structure BuilderInterface {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (safe : Out → Prop := fun _ => True) : Prop where
  chars : ByteWriterInterface ops.unsafeOps ops.outputBytes (fun out => (ops.outputSize out).val)
    (fun c => ops.argumentBytes (.char c)) safe
  sizes : ∀ arg, (stringArgSize ops arg).val = Int.ofNat (ops.argumentBytes arg).length
  allocate : ∀ n out, ops.allocate n = .ok out →
    ops.outputBytes out = [] ∧ (ops.outputSize out).val = n.val
  allocateSafe : ∀ n out, ops.allocate n = .ok out → safe out
  copyString : ∀ out s offset result,
    offset.val = Int.ofNat (ops.outputBytes out).length + 1 →
    Int.ofNat (ops.outputBytes out).length + Int.ofNat (ops.argumentBytes (.string s)).length ≤
      (ops.outputSize out).val →
    ops.unsafeOps.copyString out s offset (ops.unsafeOps.sizeofString s) = .ok result →
      ops.outputBytes result = ops.outputBytes out ++ ops.argumentBytes (.string s) ∧
      ops.outputSize result = ops.outputSize out ∧ (safe out → safe result)
  copySubString : ∀ out s offset result,
    offset.val = Int.ofNat (ops.outputBytes out).length + 1 →
    Int.ofNat (ops.outputBytes out).length + Int.ofNat (ops.argumentBytes (.substring s)).length ≤
      (ops.outputSize out).val →
    ops.unsafeOps.copySubString out s offset (ops.unsafeOps.sizeofSubString s) = .ok result →
      ops.outputBytes result = ops.outputBytes out ++ ops.argumentBytes (.substring s) ∧
      ops.outputSize result = ops.outputSize out ∧ (safe out → safe result)
  copySymbol : ∀ out s offset result,
    offset.val = Int.ofNat (ops.outputBytes out).length + 1 →
    Int.ofNat (ops.outputBytes out).length + Int.ofNat (ops.argumentBytes (.symbol s)).length ≤
      (ops.outputSize out).val →
    ops.unsafeOps.copySymbol out s offset (ops.unsafeOps.sizeofSymbol s) = .ok result →
      ops.outputBytes result = ops.outputBytes out ++ ops.argumentBytes (.symbol s) ∧
      ops.outputSize result = ops.outputSize out ∧ (safe out → safe result)

private theorem writeStringArg_bytes {C S Sym Out E : Type}
    (ops : StringBuilderOps C S Sym Out E) {safe : Out → Prop} (laws : BuilderInterface ops safe)
    (arg : StringArg C S Sym) (out result : Out) (offset n : Index)
    (hstart : offset.val = Int.ofNat (ops.outputBytes out).length + 1)
    (hfit : Int.ofNat (ops.outputBytes out).length + Int.ofNat (ops.argumentBytes arg).length ≤
      (ops.outputSize out).val)
    (hmax : (ops.outputSize out).val < IntTy.max .i64)
    (h : writeStringArg ops out offset arg = .ok (result, n)) :
    ops.outputBytes result = ops.outputBytes out ++ ops.argumentBytes arg ∧
    (ops.outputSize result).val = (ops.outputSize out).val ∧
    n.val = Int.ofNat (ops.argumentBytes arg).length ∧ (safe out → safe result) := by
  cases arg with
  | char c =>
    have hc := unsafeStringChar_bytes ops.unsafeOps _ _ _ laws.chars out result c offset n
      hstart hfit hmax h
    exact ⟨hc.1, hc.2.1, by rw [hc.2.2.1]; exact laws.chars.width c, hc.2.2.2⟩
  | string s =>
    change (do let out ← ops.unsafeOps.copyString out s offset (ops.unsafeOps.sizeofString s)
               pure (out, ops.unsafeOps.sizeofString s)) = .ok (result, n) at h
    cases hc : ops.unsafeOps.copyString out s offset (ops.unsafeOps.sizeofString s) with
    | error e => simp [hc] at h
    | ok next =>
      simp [hc] at h
      rcases h with ⟨rfl, rfl⟩
      have he := laws.copyString _ _ _ _ hstart hfit hc
      exact ⟨he.1, congrArg Subtype.val he.2.1, laws.sizes (.string s), he.2.2⟩
  | substring s =>
    change (do let out ← ops.unsafeOps.copySubString out s offset (ops.unsafeOps.sizeofSubString s)
               pure (out, ops.unsafeOps.sizeofSubString s)) = .ok (result, n) at h
    cases hc : ops.unsafeOps.copySubString out s offset (ops.unsafeOps.sizeofSubString s) with
    | error e => simp [hc] at h
    | ok next =>
      simp [hc] at h
      rcases h with ⟨rfl, rfl⟩
      have he := laws.copySubString _ _ _ _ hstart hfit hc
      exact ⟨he.1, congrArg Subtype.val he.2.1, laws.sizes (.substring s), he.2.2⟩
  | symbol s =>
    change (do let out ← ops.unsafeOps.copySymbol out s offset (ops.unsafeOps.sizeofSymbol s)
               pure (out, ops.unsafeOps.sizeofSymbol s)) = .ok (result, n) at h
    cases hc : ops.unsafeOps.copySymbol out s offset (ops.unsafeOps.sizeofSymbol s) with
    | error e => simp [hc] at h
    | ok next =>
      simp [hc] at h
      rcases h with ⟨rfl, rfl⟩
      have he := laws.copySymbol _ _ _ _ hstart hfit hc
      exact ⟨he.1, congrArg Subtype.val he.2.1, laws.sizes (.symbol s), he.2.2⟩

private theorem writeStringArgs_bytes {C S Sym Out E : Type}
    (ops : StringBuilderOps C S Sym Out E) {safe : Out → Prop} (laws : BuilderInterface ops safe) :
    ∀ args out offset result final,
    offset.val = Int.ofNat (ops.outputBytes out).length + 1 →
    Int.ofNat (ops.outputBytes out).length +
      Int.ofNat (args.map ops.argumentBytes).flatten.length ≤ (ops.outputSize out).val →
    (ops.outputSize out).val < IntTy.max .i64 →
    writeStringArgs ops args out offset = .ok (result, final) →
    ops.outputBytes result = ops.outputBytes out ++ (args.map ops.argumentBytes).flatten ∧
    (ops.outputSize result).val = (ops.outputSize out).val ∧
    final.val = Int.ofNat (ops.outputBytes result).length + 1 ∧ (safe out → safe result) := by
  intro args
  induction args with
  | nil =>
    intro out offset result final hs hf hm h
    simp [writeStringArgs] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨by simp, rfl, hs, id⟩
  | cons arg args ih =>
    intro out offset result final hs hf hm h
    have hlen : (List.map ops.argumentBytes (arg :: args)).flatten.length =
        (ops.argumentBytes arg).length + (args.map ops.argumentBytes).flatten.length := by simp
    rw [hlen, ofNat_add] at hf
    have htailnonneg : 0 ≤ Int.ofNat (args.map ops.argumentBytes).flatten.length :=
      Int.natCast_nonneg _
    have hargnonneg : 0 ≤ Int.ofNat (ops.argumentBytes arg).length := Int.natCast_nonneg _
    have hprefixnonneg : 0 ≤ Int.ofNat (ops.outputBytes out).length := Int.natCast_nonneg _
    simp only [writeStringArgs] at h
    cases hc : writeStringArg ops out offset arg with
    | error e => simp [hc] at h
    | ok pair =>
      rcases pair with ⟨next, n⟩
      simp only [hc, bind_ok] at h
      have he := writeStringArg_bytes ops laws arg out next offset n hs (by omega) hm hc
      have hn := he.2.2.1
      have hnext : (offset + n).val = Int.ofNat (ops.outputBytes next).length + 1 := by
        have ha : (offset + n).val = offset.val + n.val := add_val _ _ (by
          change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
          change (ops.outputSize out).val < 9223372036854775807 at hm
          omega)
        rw [ha, he.1, List.length_append, ofNat_add]
        omega
      have hfitnext : Int.ofNat (ops.outputBytes next).length +
          Int.ofNat (args.map ops.argumentBytes).flatten.length ≤ (ops.outputSize next).val := by
        rw [he.1, List.length_append, ofNat_add, he.2.1]
        omega
      obtain ⟨hb, hsize, hfinal, hsafe⟩ := ih next (offset + n) result final hnext hfitnext
        (by rw [he.2.1]; exact hm) h
      refine ⟨?_, hsize.trans he.2.1, hfinal, fun hs => hsafe (he.2.2.2 hs)⟩
      simpa [he.1, List.append_assoc] using hb

private theorem sizingLoop_exact {C S Sym Out E : Type}
    (ops : StringBuilderOps C S Sym Out E) {safe : Out → Prop} (laws : BuilderInterface ops safe) :
    ∀ (args : List (StringArg C S Sym)) (acc : Index), 0 ≤ acc.val →
    acc.val + Int.ofNat (args.map ops.argumentBytes).flatten.length ≤ IntTy.max .i64 →
    (args.foldl (fun total arg => total + stringArgSize ops arg) acc).val =
      acc.val + Int.ofNat (args.map ops.argumentBytes).flatten.length := by
  intro args
  induction args with
  | nil => intro acc ha hm; simp
  | cons arg args ih =>
    intro acc ha hm
    have hlen : (List.map ops.argumentBytes (arg :: args)).flatten.length =
        (ops.argumentBytes arg).length + (args.map ops.argumentBytes).flatten.length := by simp
    rw [hlen, ofNat_add] at hm
    have hn : 0 ≤ Int.ofNat (ops.argumentBytes arg).length := Int.natCast_nonneg _
    have ht : 0 ≤ Int.ofNat (args.map ops.argumentBytes).flatten.length := Int.natCast_nonneg _
    have hadd : (acc + stringArgSize ops arg).val =
        acc.val + Int.ofNat (ops.argumentBytes arg).length := by
      rw [add_val, laws.sizes]
      change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
      change acc.val + _ ≤ 9223372036854775807 at hm
      rw [laws.sizes]
      omega
    simp only [List.foldl_cons]
    rw [ih _ (by rw [hadd]; omega) (by rw [hadd]; omega), hadd]
    simp only [List.map_cons, List.flatten_cons, List.length_append, ofNat_add]
    omega

/-- String construction writes the encoded argument bytes in order and sizes them exactly. -/
def StringBuilderWritesInBounds : Prop :=
  ∀ {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (args : List (StringArg C S Sym)) (out : Out) (safe : Out → Prop),
    BuilderInterface ops safe →
    Int.ofNat (args.map ops.argumentBytes).flatten.length < IntTy.max .i64 →
    buildString ops args = .ok out →
      ops.outputBytes out = (args.map ops.argumentBytes).flatten ∧
      (ops.outputSize out).val = Int.ofNat (args.map ops.argumentBytes).flatten.length ∧ safe out

theorem stringBuilderWritesInBounds_proven : StringBuilderWritesInBounds := by
  intro C S Sym Out E ops args out safe laws hmax h
  have htotal := sizingLoop_exact ops laws args zero (by simp [zero_val])
    (by rw [zero_val]; omega)
  rw [zero_val, Int.zero_add] at htotal
  unfold buildString at h
  cases ha : ops.allocate (args.foldl (fun total arg => total + stringArgSize ops arg) zero) with
  | error e => simp [ha] at h
  | ok allocated =>
    simp only [ha, bind_ok] at h
    have hal := laws.allocate _ _ ha
    cases hw : writeStringArgs ops args allocated one with
    | error e => simp [hw] at h
    | ok pair =>
      rcases pair with ⟨result, final⟩
      simp [hw] at h
      subst out
      have he := writeStringArgs_bytes ops laws args allocated one result final
        (by rw [one_val, hal.1]; rfl)
        (by rw [hal.1, hal.2, htotal]; simp)
        (by rw [hal.2, htotal]; exact hmax) hw
      exact ⟨by simpa [hal.1] using he.1, he.2.1.trans (hal.2.trans htotal),
        he.2.2.2 (laws.allocateSafe _ _ ha)⟩

/-- The iterator yields these characters in this order and then terminates.
This constrains only the external iterator, not the filter or predicate. -/
inductive FilterTrace {S C Out E Result : Type} (ops : FilterOps S C Out E Result)
    (s : S) : List UInt8 → Index → List C → Prop where
  | done (remaining state) : ops.iterate s remaining state = .ok none →
      FilterTrace ops s remaining state []
  | step (remaining state) (next : FilterNext C remaining) (cs : List C) :
      ops.iterate s remaining state = .ok (some next) →
      FilterTrace ops s next.tail next.state cs →
      FilterTrace ops s remaining state (next.char :: cs)

private theorem filterIteration_eq {S C Out E Result : Type}
    (ops : FilterOps S C Out E Result) (s : S) (remaining : List UInt8) (state : Index) (cs : List C)
    (trace : FilterTrace ops s remaining state cs) :
    ∀ out offset, filterIteration ops s remaining state out offset = filterCharacters ops cs out offset := by
  induction trace with
  | done remaining state hdone =>
    intro out offset
    rw [filterIteration]
    simp [filterCharacters, hdone]
  | step remaining state next cs hstep trace ih =>
    intro out offset
    rw [filterIteration]
    simp only [hstep, bind_ok, filterCharacters]
    cases hp : ops.predicate next.char with
    | false => simpa [hp] using ih out offset
    | true =>
      simp only [ite_true]
      cases hw : unsafeStringChar ops.unsafeOps out next.char offset with
      | error e => simp
      | ok pair =>
        rcases pair with ⟨written, n⟩
        simp only [bind_ok]
        exact ih written (offset + n)

/-- Character encoding, allocation, resizing, and String decoding are external interfaces. -/
structure FilterInterface {S C Out E Result : Type} (ops : FilterOps S C Out E Result)
    (bytes : Out → List Nat) (capacity : Out → Int) (encode : C → List Nat) : Prop where
  chars : ByteWriterInterface ops.unsafeOps bytes capacity encode
  inputSize : ∀ s cs, ops.characters s = .ok cs →
    Int.ofNat (cs.map encode).flatten.length = (ops.sizeof s).val
  iteration : ∀ s cs, ops.characters s = .ok cs →
    FilterTrace ops s (ops.codeunits s) (ops.firstindex s) cs
  allocate : ∀ n out, ops.allocate n = .ok out → bytes out = [] ∧ capacity out = n.val
  resize : ∀ out n result, n.val = Int.ofNat (bytes out).length →
    ops.resize out n = .ok result → bytes result = bytes out
  sizehint : ∀ out n result, ops.sizehint out n = .ok result → bytes result = bytes out
  decode : ∀ out result cs, bytes out = (cs.map encode).flatten →
    ops.toString out = .ok result → ops.outputCharacters result = .ok cs

private theorem filterCharacters_bytes {S C Out E Result : Type}
    (ops : FilterOps S C Out E Result) (bytes : Out → List Nat)
    (capacity : Out → Int) (encode : C → List Nat)
    (laws : FilterInterface ops bytes capacity encode) :
    ∀ cs out offset result final,
    offset.val = Int.ofNat (bytes out).length + 1 →
    Int.ofNat (bytes out).length + Int.ofNat (cs.map encode).flatten.length ≤ capacity out →
    capacity out < IntTy.max .i64 →
    filterCharacters ops cs out offset = .ok (result, final) →
      bytes result = bytes out ++ ((cs.filter ops.predicate).map encode).flatten ∧
      capacity result = capacity out ∧ final.val = Int.ofNat (bytes result).length + 1 := by
  intro cs
  induction cs with
  | nil =>
    intro out offset result final hs hf hm h
    simp [filterCharacters] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨by simp, rfl, hs⟩
  | cons c cs ih =>
    intro out offset result final hs hf hm h
    have hlen : (List.map encode (c :: cs)).flatten.length =
        (encode c).length + (cs.map encode).flatten.length := by simp
    rw [hlen, ofNat_add] at hf
    have htailnonneg : 0 ≤ Int.ofNat (cs.map encode).flatten.length := Int.natCast_nonneg _
    have hcharNonneg : 0 ≤ Int.ofNat (encode c).length := Int.natCast_nonneg _
    have hprefixnonneg : 0 ≤ Int.ofNat (bytes out).length := Int.natCast_nonneg _
    cases hp : ops.predicate c with
    | false =>
      simp [filterCharacters, hp] at h
      obtain ⟨hb, hc, hend⟩ := ih out offset result final hs (by omega) hm h
      exact ⟨by simpa [hp] using hb, hc, hend⟩
    | true =>
      simp only [filterCharacters, hp, ite_true] at h
      cases hw : unsafeStringChar ops.unsafeOps out c offset with
      | error e => simp [hw] at h
      | ok pair =>
        rcases pair with ⟨next, n⟩
        simp only [hw, bind_ok] at h
        have he := unsafeStringChar_bytes ops.unsafeOps bytes capacity encode laws.chars
          out next c offset n hs (by omega) hm hw
        have hn : n.val = Int.ofNat (encode c).length := by
          rw [he.2.2.1]; exact laws.chars.width c
        have hnext : (offset + n).val = Int.ofNat (bytes next).length + 1 := by
          have ha : (offset + n).val = offset.val + n.val := add_val _ _ (by
            change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
            change capacity out < 9223372036854775807 at hm
            omega)
          rw [ha, he.1, List.length_append, ofNat_add]
          omega
        have hfitnext : Int.ofNat (bytes next).length +
            Int.ofNat (cs.map encode).flatten.length ≤ capacity next := by
          rw [he.1, List.length_append, ofNat_add, he.2.1]
          omega
        obtain ⟨hb, hc, hend⟩ := ih next (offset + n) result final hnext hfitnext
          (by rw [he.2.1]; exact hm) h
        exact ⟨by simpa [hp, he.1, List.append_assoc] using hb, hc.trans he.2.1, hend⟩


/-- Filtering retains accepted characters in their original order. -/
def FilterKeepsAcceptedCharacters : Prop :=
  ∀ {S C Out E Result : Type} (ops : FilterOps S C Out E Result)
    (bytes : Out → List Nat) (capacity : Out → Int) (encode : C → List Nat)
    (s : S) (chars : List C) (result : Result),
    FilterInterface ops bytes capacity encode →
    (ops.sizeof s).val < IntTy.max .i64 →
    ops.characters s = .ok chars → filterString ops s = .ok result →
      ops.outputCharacters result = .ok (chars.filter ops.predicate)

theorem filterKeepsAcceptedCharacters_proven : FilterKeepsAcceptedCharacters := by
  intro S C Out E Result ops bytes capacity encode s chars result laws hmax hc h
  unfold filterString at h
  cases ha : ops.allocate (ops.sizeof s) with
  | error e => simp [ha] at h
  | ok allocated =>
    simp only [ha, bind_ok, filterIteration_eq ops s _ _ _ (laws.iteration s chars hc)] at h
    have hal := laws.allocate _ _ ha
    cases hw : filterCharacters ops chars allocated one with
    | error e => simp [hw] at h
    | ok pair =>
      rcases pair with ⟨next, offset⟩
      simp only [hw, bind_ok] at h
      have he := filterCharacters_bytes ops bytes capacity encode laws chars allocated one next offset
        (by rw [hal.1, one_val]; rfl)
        (by rw [hal.1, hal.2, ← laws.inputSize _ _ hc]; simp)
        (by rw [hal.2]; exact hmax) hw
      have hoff : (offset - one).val = Int.ofNat (bytes next).length := by
        have hp : 0 ≤ Int.ofNat (bytes next).length := Int.natCast_nonneg _
        rw [sub_one_val offset (by omega), he.2.2]
        omega
      cases hr : ops.resize next (offset - one) with
      | error e => simp [hr] at h
      | ok resized =>
        simp only [hr, bind_ok] at h
        have hresize := laws.resize _ _ _ hoff hr
        cases hh : ops.sizehint resized (offset - one) with
        | error e => simp [hh] at h
        | ok hinted =>
          simp only [hh, bind_ok] at h
          have hhint := laws.sizehint _ _ _ hh
          apply laws.decode hinted result (chars.filter ops.predicate) _ h
          rw [hhint, hresize, he.1, hal.1, List.nil_append]

/-- Valid endpoint construction preserves both the parent and the exact byte extent. -/
def ViewConstructorPreservesParent : Prop :=
  (∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (s : S)
      (i j next : Index) (ss : SubString S),
    1 ≤ i.val → i.val ≤ j.val → j.val < next.val →
    ops.checkboundsRange s i j = .ok () →
    ops.isvalid s i = .ok true → ops.isvalid s j = .ok true →
    ops.nextind s j = .ok next →
    typedSubString ops s i j = .ok ss →
      ss.string = s ∧ ss.offset.val = i.val - 1 ∧
      0 < ss.ncodeunits.val ∧ ss.offset.val + ss.ncodeunits.val = next.val - 1) ∧
  (∀ {S C CT E : Type} (ops : SubStringOps S C CT E)
      (ss : SubString S) (i j : Index) (e : E),
    i.val ≤ j.val → ops.checkboundsViewRange ss i j = .error e →
      subStringNested ops ss i j = .error e)

/-- A view invariant describes parent storage independently of any implementation. -/
def ValidView {S : Type} (parentLength : S → Index) (ss : SubString S) : Prop :=
  0 ≤ ss.offset.val ∧ 0 ≤ ss.ncodeunits.val ∧
    ss.offset.val + ss.ncodeunits.val ≤ (parentLength ss.string).val

/-- Nested construction translates both endpoints without changing the parent allocation. -/
def NestedViewInterval : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E)
    (ss result : SubString S) (i j next : Index),
    ValidView ops.ncodeunits ss →
    1 ≤ i.val → i.val ≤ j.val → j.val ≤ ss.ncodeunits.val →
    (ss.offset + j).val < next.val →
    ops.checkboundsRange ss.string (ss.offset + i) (ss.offset + j) = .ok () →
    ops.isvalid ss.string (ss.offset + i) = .ok true →
    ops.isvalid ss.string (ss.offset + j) = .ok true →
    ops.nextind ss.string (ss.offset + j) = .ok next →
    subStringNested ops ss i j = .ok result →
      result.string = ss.string ∧ result.offset.val = ss.offset.val + i.val - 1 ∧
      0 < result.ncodeunits.val ∧
      result.offset.val + result.ncodeunits.val = next.val - 1

def AllViewConstructors : Prop :=
  ViewConstructorPreservesParent ∧ NestedViewInterval

/-- Invalid local reads fail independently of every possible parent-index and parent-read
implementation. Scalar bounds checks are the definitions from `basic.jl`. -/
def InvalidReadsRejected : Prop :=
  ∀ {S I P V E : Type} (value : I → Int) (ss : SubString S) (i : I) (error : E)
    (parentIndex : Index → I → Except E P) (read : S → P → Except E V)
    (parentValid : S → P → Except E Bool),
    (value i < 1 ∨ ss.ncodeunits.val < value i) →
    let check := fun ss i => JuliaLean.base.strings.basic.checkboundsScalar ncodeunitsSubString
      (fun i => decide (1 ≤ value i)) (fun i n => decide (value i ≤ n.val)) ss i
    getindexSubString (fun ss i => JuliaLean.base.strings.basic.checkboundsThrow (.ok (check ss i)) error)
      parentIndex read ss i = .error error ∧
    codeunitSubStringAt (fun ss i => JuliaLean.base.strings.basic.checkboundsThrow (.ok (check ss i)) error)
      parentIndex read ss i = .error error ∧
    isvalidSubStringAt (fun ss i => .ok (check ss i)) parentIndex parentValid ss i = .ok false

def InvalidConstructorsRejected : Prop :=
  (∀ {S C CT E : Type} (ops : SubStringOps S C CT E)
      (s : S) (i j : Index) (error : E),
    i.val ≤ j.val →
    (i.val < 1 ∨ (ops.ncodeunits s).val < j.val) →
    (∀ first last, first.val ≤ last.val →
      (first.val < 1 ∨ (ops.ncodeunits s).val < last.val) →
      ops.checkboundsRange s first last = .error error) →
    typedSubString ops s i j = .error error) ∧
  (∀ {S C CT E : Type} (ops : SubStringOps S C CT E)
      (ss : SubString S) (i j : Index) (error : E),
    i.val ≤ j.val → (i.val < 1 ∨ ss.ncodeunits.val < j.val) →
    (∀ first last, first.val ≤ last.val →
      (first.val < 1 ∨ ss.ncodeunits.val < last.val) →
      ops.checkboundsViewRange ss first last = .error error) →
    subStringNested ops ss i j = .error error)

def InvalidCharacterEndpointsRejected : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (s : S) (i j : Index),
    i.val ≤ j.val →
    ops.checkboundsRange s i j = .ok () →
    (ops.isvalid s i = .ok false →
      typedSubString ops s i j = .error (ops.stringIndexError s i)) ∧
    (ops.isvalid s i = .ok true → ops.isvalid s j = .ok false →
      typedSubString ops s i j = .error (ops.stringIndexError s j))

def RawSubstringAllWithinParent : Prop :=
  RawSubstringWithinParent ∧
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (ss result : SubString S)
    (first count : Index),
    ValidView ops.ncodeunits ss →
    rawSubstringView ops ss first count = .ok result →
      result.string = ss.string ∧ ValidView ops.ncodeunits result

def SubstringValidity : Prop :=
  ∀ {S I P E : Type}
    (checkbounds : SubString S → I → Except E Bool)
    (parentIndex : Index → I → Except E P)
    (isvalid : S → P → Except E Bool) (ss : SubString S) (i : I),
    (checkbounds ss i = .ok false →
      isvalidSubStringAt checkbounds parentIndex isvalid ss i = .ok false) ∧
    (isvalidSubStringAt checkbounds parentIndex isvalid ss i = .ok true →
      ∃ p, checkbounds ss i = .ok true ∧ parentIndex ss.offset i = .ok p ∧
        isvalid ss.string p = .ok true)

/-- Checked character and byte reads cannot reach outside the parent allocation. -/
def SubstringReadUsesParent : Prop :=
  ∀ {S I P V E : Type} (parentLength : S → Index)
    (indexValue : I → Int) (parentValue : P → Int)
    (checkbounds : SubString S → I → Except E Unit)
    (parentIndex : Index → I → Except E P)
    (read : S → P → Except E V) (ss : SubString S) (i : I) (v : V),
    ValidView parentLength ss →
    (checkbounds ss i = .ok () → 1 ≤ indexValue i ∧ indexValue i ≤ ss.ncodeunits.val) →
    (∀ p, parentIndex ss.offset i = .ok p → parentValue p = ss.offset.val + indexValue i) →
    (getindexSubString checkbounds parentIndex read ss i = .ok v ∨
      codeunitSubStringAt checkbounds parentIndex read ss i = .ok v) →
    ∃ p, read ss.string p = .ok v ∧
      parentValue p = ss.offset.val + indexValue i ∧
      1 ≤ parentValue p ∧ parentValue p ≤ (parentLength ss.string).val

/-- Character length counts the parent character starts within the view's byte interval. -/
def SubstringViewIntervalSemantics : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E)
    (starts : S → List Int) (ss : SubString S) (len : Index),
    0 ≤ ss.offset.val → 0 ≤ ss.ncodeunits.val →
    ss.offset.val + ss.ncodeunits.val < IntTy.max .i64 →
    (∀ first last n, ops.length ss.string first last = .ok n →
      n.val = Int.ofNat ((starts ss.string).filter
        (fun k => decide (first.val ≤ k ∧ k ≤ last.val))).length) →
    (lengthSubString ops ss = .ok len ∨ lengthStringSubString ops ss = .ok len) →
      len.val = Int.ofNat ((starts ss.string).filter
        (fun k => decide (ss.offset.val < k ∧ k ≤ ss.offset.val + ss.ncodeunits.val))).length

def WholeViewSemantics : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (s : S) (len : Index),
    0 ≤ (ops.ncodeunits s).val →
    ops.length s one (ops.ncodeunits s) = .ok len →
    lengthSubString ops (typedWholeSubString ops s) = .ok len ∧
    ∃ ss, subStringWhole ops s = .ok ss ∧
      lengthSubString ops ss = .ok len ∧ parentSubString ss = s

def SubstringAllViewIntervals : Prop :=
  SubstringViewIntervalSemantics ∧ WholeViewSemantics

def SubstringIndexInBounds : Prop :=
  RawSubstringAllWithinParent ∧ SubstringReadUsesParent ∧
    AllViewConstructors ∧ SubstringValidity ∧ InvalidReadsRejected ∧
    InvalidConstructorsRejected ∧ InvalidCharacterEndpointsRejected

/-- Pointer addition is measured in bytes; hashing is independent of storage identity. -/
def SubstringPointerUsesParentOffset : Prop :=
  (∀ {S : Type} (ops : PointerOps S) (address : ops.Pointer → Int)
      (ss : SubString S),
    (∀ p i, address (ops.add p i) = address p + i.val) →
      address (pointerSubString ops ss) = address (ops.pointer ss.string) + ss.offset.val) ∧
  (∀ {S : Type} (ops : HashOps S)
      (bytesAt : ops.pointerOps.Pointer → Index → List Nat)
      (seed : JInt .u64) (ss tt : SubString S),
    (∀ owner other p q n m h secret, bytesAt p n = bytesAt q m →
      ops.hashBytes owner p n h secret = ops.hashBytes other q m h secret) →
    bytesAt (pointerSubString ops.pointerOps ss) (ops.sizeof ss) =
      bytesAt (pointerSubString ops.pointerOps tt) (ops.sizeof tt) →
      hashSubString ops seed ss = hashSubString ops seed tt) ∧
  (∀ {S I J : Type} (ops : PointerOps S)
      (subtractOne : I → J) (indexValue : I → Int) (deltaValue : J → Int)
      (add : ops.Pointer → J → Except JlError ops.Pointer)
      (address : ops.Pointer → Int) (ss : SubString S) (i : I) (p : ops.Pointer),
    deltaValue (subtractOne i) = indexValue i - 1 →
    (∀ p k, address (ops.add p k) = address p + k.val) →
    (∀ p k result, add p k = .ok result → address result = address p + deltaValue k) →
    pointerSubStringAt ops subtractOne add ss i = .ok p →
      address p = address (ops.pointer ss.string) + ss.offset.val + indexValue i - 1) ∧
  (∀ {S P E : Type} (ops : PointerOps S)
      (convert : ops.Pointer → Except E P) (add : P → Index → Except E P)
      (address : ops.Pointer → Int) (convertedAddress : P → Int) (ss : SubString S) (p : P),
    (∀ p q, convert p = .ok q → convertedAddress q = address p) →
    (∀ p k q, add p k = .ok q → convertedAddress q = convertedAddress p + k.val) →
    unsafeConvertSubString ops convert add ss = .ok p →
      convertedAddress p = address (ops.pointer ss.string) + ss.offset.val)

/-- Conversion preserves the externally converted string's bytes as a whole view. -/
def SubstringConversions : Prop :=
  ∀ {A S C CT E : Type} (ops : SubStringOps S C CT E)
    (convert : A → Except E S) (assertType : SubString S → Except E (SubString S))
    (bytes : S → List Nat) (s : A) (parent : S) (ss : SubString S),
    (∀ view, assertType view = .ok view) →
    convert s = .ok parent →
    (ops.ncodeunits parent).val = Int.ofNat (bytes parent).length →
    convertSubString convert (subStringWhole ops) assertType s = .ok ss →
      bytes (parentSubString ss) = bytes parent ∧
      (ncodeunitsSubString ss).val = Int.ofNat (bytes parent).length ∧ ss.offset.val = 0

def NestedSubstringConversion : Prop :=
  ∀ {A S E : Type} (convert : A → Except E (SubString S))
    (assertType : SubString S → Except E (SubString (SubString S)))
    (s : A) (parent : SubString S) (error : E),
    convert s = .ok parent →
    (∀ view, assertType view = .error error) →
    convertSubString convert subStringWholeView assertType s = .error error

def SubstringConversionSemantics : Prop :=
  SubstringConversions ∧ NestedSubstringConversion

/-- Byte equality is reflexive and agrees with equality of the complete byte sequences.
Comparison of a view with itself is zero. The hypotheses are the `_memcmp` and integer
comparison interface contracts, independent of these methods. -/
def SubstringComparison : Prop :=
  (∀ {S : Type} (sizeof : S → Index) (memcmp : S → S → Index)
      (bytes : S → List Nat) (a b : S),
    (∀ s, (sizeof s).val = Int.ofNat (bytes s).length) →
    ((sizeof a).val = (sizeof b).val →
      ((memcmp a b).val = 0 ↔ bytes a = bytes b)) →
      (equalStringViews sizeof memcmp a b = true ↔ bytes a = bytes b)) ∧
  (∀ {S : Type} (memcmp : S → S → Index) (sizeof : S → Index)
      (cmpIndex : Index → Index → Index) (a : S),
    (memcmp a a).val = 0 → (∀ n, (cmpIndex n n).val = 0) →
      (cmpSubString memcmp sizeof cmpIndex a a).val = 0)

/-- String conversion returns exactly the selected bytes, rather than exposing parent bytes. -/
def StringConversionCopiesView : Prop :=
  ∀ {S Out E : Type} (ops : CopyStringOps S Out E)
    (bytes : S → List Nat) (outputBytes : Out → List Nat)
    (ss : SubString S) (out : Out),
    (∀ offset count result,
      ops.unsafeString ss.string (ops.pointer ss.string (offset + one)) count = .ok result →
      outputBytes result = ((bytes ss.string).drop offset.val.toNat).take count.val.toNat) →
    (stringFromSubString ops ss = .ok out ∨ stringSubString ops ss = .ok out) →
      outputBytes out = ((bytes ss.string).drop ss.offset.val.toNat).take ss.ncodeunits.val.toNat

theorem rawSubstringWithinParent_proven : RawSubstringWithinParent := by
  intro S C CT E ops s first count ss hn h
  unfold rawSubstring at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.true_and, Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
    have hi : 1 ≤ first.val := by omega
    have hav := available_val (ops.ncodeunits s) first hn hi
    simp only [pure, Except.pure, Except.ok.injEq] at h
    cases h
    simp only [sub_one_val first hi]
    exact ⟨True.intro, by omega, by omega, by omega⟩

theorem rawSubstringAllWithinParent_proven : RawSubstringAllWithinParent := by
  refine ⟨rawSubstringWithinParent_proven, ?_⟩
  intro S C CT E ops ss result first count hv h
  unfold rawSubstringView at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.true_and, Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
    have hi : 1 ≤ first.val := by omega
    obtain ⟨ho, hn, hbound⟩ := hv
    have hav := available_val ss.ncodeunits first hn hi
    have hp := (ops.ncodeunits ss.string).property
    have hfirst : first.val + ss.offset.val ≤ (ops.ncodeunits ss.string).val + 1 := by omega
    have hoff : (first + ss.offset - one).val = first.val + ss.offset.val - 1 := by
      by_cases he : first.val + ss.offset.val ≤ IntTy.max .i64
      · have hsum : (first + ss.offset).val = first.val + ss.offset.val :=
          add_val _ _ (by
            change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
            change first.val + ss.offset.val ≤ 9223372036854775807 at he
            omega)
        rw [sub_one_val _ (by rw [hsum]; omega), hsum]
      · have hend : first.val + ss.offset.val = IntTy.max .i64 + 1 := by omega
        change wrapInt .i64 (wrapInt .i64 (first.val + ss.offset.val) - one.val) =
          first.val + ss.offset.val - 1
        rw [hend, one_val]
        decide
    simp only [pure_ok, Except.ok.injEq] at h
    cases h
    change ss.string = ss.string ∧ 0 ≤ (first + ss.offset - one).val ∧
      0 ≤ count.val ∧ (first + ss.offset - one).val + count.val ≤ (ops.ncodeunits ss.string).val
    rw [hoff]
    exact ⟨rfl, by omega, by omega, by omega⟩

theorem substringValidity_proven : SubstringValidity := by
  intro S I P E checkbounds parentIndex isvalid ss i
  constructor
  · intro h
    simp [isvalidSubStringAt, h]
  · intro h
    unfold isvalidSubStringAt at h
    cases hb : checkbounds ss i with
    | error e => simp [hb] at h
    | ok valid =>
      cases valid with
      | false => simp [hb] at h
      | true =>
        simp only [hb, bind_ok, ite_true] at h
        cases hp : parentIndex ss.offset i with
        | error e => simp [hp] at h
        | ok p => exact ⟨p, rfl, rfl, by simpa [hp] using h⟩

theorem substringIndexArithmetic_proven : SubstringIndexArithmetic := by
  unfold SubstringIndexArithmetic
  omega

private theorem repeatCopyBlocks_size {S Out E I : Type} (ops : RepeatOps S Out E I)
    (laws : RepeatInterface ops) (s : RepeatInput S) (n : Nat) :
    ∀ remaining i out result, repeatCopyBlocks ops s n remaining i out = .ok result →
      ops.outputSize result = ops.outputSize out := by
  intro remaining
  induction remaining with
  | zero => intro i out result h; cases h; rfl
  | succ remaining ih =>
    intro i out result h
    simp only [repeatCopyBlocks] at h
    cases hc : ops.copyBlock out s (i * n + 1) n with
    | error e => simp [hc] at h
    | ok next =>
      simp only [hc, bind_ok] at h
      exact (ih _ _ _ h).trans (laws.copyBlock _ _ _ _ _ hc)

theorem repeatSize_proven : RepeatSize := by
  intro S Out E I ops s r count out laws hc h
  cases hn : ops.isNegative r with
  | true => simp [repeatString, hn] at h
  | false =>
    simp only [repeatString, hn, Bool.false_eq_true, ite_false, hc, bind_ok] at h
    by_cases hz : count = 0
    · subst count
      simp only [beq_self_eq_true, ite_true, pure, Except.pure, Except.ok.injEq] at h
      subst out
      simp [laws.empty]
    · simp only [show (count == 0) = false from by simpa using hz, ite_false,
        Bool.false_eq_true] at h
      by_cases ho : count = 1
      · subst count
        simp only [beq_self_eq_true, ite_true] at h
        cases s with
        | string value => simpa using laws.stringCopy value out h
        | substring view =>
          have he : ops.stringCopyOps.unsafeString
              view.string (ops.stringCopyOps.pointer view.string (view.offset + one)) view.ncodeunits = .ok out := by
            simpa [stringFromSubString] using h
          simpa [laws.substringSize] using laws.unsafeString _ _ _ _ he
      · simp only [show (count == 1) = false from by simpa using ho, ite_false,
          Bool.false_eq_true] at h
        by_cases hs : ops.sizeof s = 0
        · simp [hs] at h
          subst out
          simp [laws.empty, hs]
        · simp only [show (ops.sizeof s == 0) = false from by simpa using hs,
            Bool.false_eq_true, ite_false] at h
          split at h
          · simp at h
          · cases ha : ops.allocateString (ops.sizeof s * count) with
            | error e => simp [ha] at h
            | ok allocated =>
              simp only [ha, bind_ok] at h
              have hsize := laws.allocate _ _ ha
              split at h
              · cases hb : ops.codeunitOne s with
                | error e => simp [hb] at h
                | ok b =>
                  simp only [hb, bind_ok] at h
                  rw [laws.memset _ _ _ _ h, hsize, Nat.mul_comm]
              · rw [repeatCopyBlocks_size ops laws _ _ _ _ _ _ h, hsize, Nat.mul_comm]


private def accent : JuliaLean.base.strings.basic.StringData :=
  ⟨[0xc3, 0xa9], [int 1], [0xe9]⟩


theorem rawSubstringIterates_refuted : ¬ RawSubstringIterates := by
  intro h
  have hr : rawSubstring concreteOps accent (int 1) (int 1) =
      .ok ⟨accent, int 0, int 1⟩ := by decide
  have he : collectSubString
      (iterateSubString (fun i n => decide (i.val = n.val)) checkedView
        (fun off i => .ok (off + i))
        JuliaLean.base.strings.basic.stringDataOps.iterateAt)
      JuliaLean.base.strings.basic.firstindexString ⟨accent, int 0, int 1⟩ = .error .boundsError := by decide
  rcases h accent _ _ _ hr with hsuccess | hallowedError
  · obtain ⟨chars, hc, _⟩ := hsuccess
    rw [he] at hc
    cases hc
  · rw [he] at hallowedError
    cases hallowedError.2

theorem emptySubstringOffset_refuted : ¬ EmptySubstringOffset := by
  intro h
  have he := h concreteOps accent (int 2) (int 1) ⟨accent, zero, zero⟩
    (by decide) (by decide)
  have hz : zero.val = 0 := zero_val
  have ht : (int 2).val = 2 := by decide
  change zero.val = (int 2).val - 1 at he
  omega

theorem viewConstructorPreservesParent_proven : ViewConstructorPreservesParent := by
  constructor
  · intro S C CT E ops s i j next ss hi hij hjn hb hvi hvj hn h
    have hji : ¬j.val < i.val := by omega
    simp [typedSubString, hji, hb, hvi, hvj, hn] at h
    cases h
    have hnext := next.property
    have hsub : (next - i).val = next.val - i.val := sub_val next i (by
      change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
      change -9223372036854775808 ≤ next.val ∧ next.val ≤ 9223372036854775807 at hnext
      omega)
    exact ⟨rfl, sub_one_val i hi, by change 0 < (next - i).val; rw [hsub]; omega,
      by change (i - one).val + (next - i).val = _; rw [sub_one_val i hi, hsub]; omega⟩
  · intro S C CT E ops ss i j e hij he
    simp [subStringNested, hij, he]

theorem nestedViewInterval_proven : NestedViewInterval := by
  intro S C CT E ops ss result i j next hv hi hij hj hn hb hvi hvj hnext h
  have ho := hv.1
  have hbound := hv.2.2
  have hp := (ops.ncodeunits ss.string).property
  have hival : (ss.offset + i).val = ss.offset.val + i.val := add_val _ _ (by
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    change -9223372036854775808 ≤ (ops.ncodeunits ss.string).val ∧
      (ops.ncodeunits ss.string).val ≤ 9223372036854775807 at hp
    omega)
  have hjval : (ss.offset + j).val = ss.offset.val + j.val := add_val _ _ (by
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    change -9223372036854775808 ≤ (ops.ncodeunits ss.string).val ∧
      (ops.ncodeunits ss.string).val ≤ 9223372036854775807 at hp
    omega)
  have hrun : typedSubString ops ss.string (ss.offset + i) (ss.offset + j) = .ok result := by
    simp only [subStringNested, show i.val ≤ j.val from hij, ite_true] at h
    cases hc : ops.checkboundsViewRange ss i j with
    | error e => simp [hc] at h
    | ok checked =>
      cases checked
      simpa [hc, subStringInt] using h
  have he := viewConstructorPreservesParent_proven.1 ops ss.string
    (ss.offset + i) (ss.offset + j) next result
    (by rw [hival]; omega) (by rw [hival, hjval]; omega) hn hb hvi hvj hnext hrun
  simpa [hival] using he

theorem allViewConstructors_proven : AllViewConstructors :=
  ⟨viewConstructorPreservesParent_proven, nestedViewInterval_proven⟩

theorem invalidReadsRejected_proven : InvalidReadsRejected := by
  intro S I P V E value ss i error parentIndex read parentValid hi
  by_cases hlow : 1 ≤ value i
  · have hhigh : ¬ value i ≤ ss.ncodeunits.val := by omega
    simp [getindexSubString, codeunitSubStringAt, isvalidSubStringAt,
      JuliaLean.base.strings.basic.checkboundsThrow, JuliaLean.base.strings.basic.checkboundsScalar,
      ncodeunitsSubString, hlow, hhigh]
  · simp [getindexSubString, codeunitSubStringAt, isvalidSubStringAt,
      JuliaLean.base.strings.basic.checkboundsThrow, JuliaLean.base.strings.basic.checkboundsScalar,
      ncodeunitsSubString, hlow]

theorem invalidConstructorsRejected_proven : InvalidConstructorsRejected := by
  constructor
  · intro S C CT E ops s i j error hij hi bounds
    have hn : ¬j.val < i.val := by omega
    simp [typedSubString, hn, bounds i j hij hi]
  · intro S C CT E ops ss i j error hij hi bounds
    simp [subStringNested, hij, bounds i j hij hi]

theorem invalidCharacterEndpointsRejected_proven : InvalidCharacterEndpointsRejected := by
  intro S C CT E ops s i j hij hb
  have hnot : ¬j.val < i.val := by omega
  constructor
  · intro hi
    simp [typedSubString, hnot, hb, hi]
  · intro hi hj
    simp [typedSubString, hnot, hb, hi, hj]

theorem substringReadUsesParent_proven : SubstringReadUsesParent := by
  intro S I P V E parentLength indexValue parentValue checkbounds parentIndex read ss i v hv hb hp h
  have hr : getindexSubString checkbounds parentIndex read ss i = .ok v :=
    h.elim id (fun h => h)
  unfold getindexSubString at hr
  cases hc : checkbounds ss i with
  | error e => simp [hc] at hr
  | ok checked =>
    cases checked
    have hi := hb hc
    simp only [hc, bind_ok] at hr
    cases hpi : parentIndex ss.offset i with
    | error e => simp [hpi] at hr
    | ok p =>
      simp only [hpi, bind_ok] at hr
      have he := hp p hpi
      refine ⟨p, hr, he, ?_, ?_⟩
      · rw [he]; unfold ValidView at hv; omega
      · rw [he]; unfold ValidView at hv; omega

theorem substringIndexInBounds_proven : SubstringIndexInBounds :=
  ⟨rawSubstringAllWithinParent_proven, substringReadUsesParent_proven,
    allViewConstructors_proven, substringValidity_proven,
    invalidReadsRejected_proven, invalidConstructorsRejected_proven,
    invalidCharacterEndpointsRejected_proven⟩

theorem parentIndices_proven : ParentIndices := by
  intro S C CT E ops ss starts indices ho hn hmax laws h
  have hsum : (ss.offset + ss.ncodeunits).val = ss.offset.val + ss.ncodeunits.val :=
    add_val _ _ (by
      change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
      change ss.offset.val + ss.ncodeunits.val < 9223372036854775807 at hmax
      omega)
  have hfirst : (ss.offset + one).val = ss.offset.val + 1 := by
    rw [add_val, one_val]
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    change ss.offset.val + ss.ncodeunits.val < 9223372036854775807 at hmax
    rw [one_val]
    omega
  unfold parentindicesSubString at h
  cases hl : ops.thisindParent ss.string (ss.offset + ss.ncodeunits) with
  | error e => simp [hl] at h
  | ok last =>
    simp [hl] at h
    cases h
    have hlast := laws _ _ hl
    refine ⟨hfirst, hlast.1, by simpa [hsum] using hlast.2.1, rfl, ?_, ?_⟩
    · exact hlast.2.2.elim (fun hz => Or.inl hz.1) Or.inr
    · intro hcount
      rcases hlast.2.2 with hz | hmem
      · rw [hsum] at hz
        omega
      · exact hmem

theorem substringViewIntervalSemantics_proven : SubstringViewIntervalSemantics := by
  intro S C CT E ops starts ss len ho hn hmax laws h
  have hsum : (ss.offset + ss.ncodeunits).val = ss.offset.val + ss.ncodeunits.val :=
    add_val _ _ (by
      change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
      change ss.offset.val + ss.ncodeunits.val < 9223372036854775807 at hmax
      omega)
  have hfirst : (ss.offset + one).val = ss.offset.val + 1 := by
    rw [add_val, one_val]
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    change ss.offset.val + ss.ncodeunits.val < 9223372036854775807 at hmax
    rw [one_val]
    omega
  have hr : ops.length ss.string (ss.offset + one) (ss.offset + ss.ncodeunits) = .ok len :=
    h.elim id id
  have he := laws _ _ _ hr
  rw [hfirst, hsum] at he
  have hp : (fun k => decide (ss.offset.val + 1 ≤ k ∧ k ≤ ss.offset.val + ss.ncodeunits.val)) =
      (fun k => decide (ss.offset.val < k ∧ k ≤ ss.offset.val + ss.ncodeunits.val)) := by
    funext k
    congr 1
  rwa [hp] at he

theorem substringPointerUsesParentOffset_proven : SubstringPointerUsesParentOffset := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S ops address ss laws
    exact laws _ _
  · intro S ops bytesAt seed ss tt laws he
    unfold hashSubString
    rw [laws ss tt _ _ _ _ _ _ he]
  · intro S I J ops subtractOne indexValue deltaValue add address ss i p hsub hadd hchecked h
    change add (ops.add (ops.pointer ss.string) ss.offset) (subtractOne i) = .ok p at h
    rw [hchecked _ _ _ h, hadd, hsub]
    omega
  · intro S P E ops convert add address convertedAddress ss p hconvert hadd h
    unfold unsafeConvertSubString at h
    cases hc : convert (ops.pointer ss.string) with
    | error e => simp [hc] at h
    | ok q =>
      simp only [hc, bind_ok] at h
      rw [hadd _ _ _ h, hconvert _ _ hc]

theorem substringConversions_proven : SubstringConversions := by
  intro A S C CT E ops convert assertType bytes s parent ss assertLaw hc hn h
  have he : subStringWhole ops parent = .ok ss := by
    simp only [convertSubString, hc, bind_ok] at h
    cases hrun : subStringWhole ops parent with
    | error e => simp [hrun] at h
    | ok view =>
      simp [hrun, assertLaw] at h
      subst ss
      rfl
  have hr : ss.string = parent ∧ ss.offset = zero ∧ ss.ncodeunits = ops.ncodeunits parent := by
    have hz : one - one = zero := by decide
    simp [subStringWhole, rawSubstring, hz] at he
    cases he
    exact ⟨rfl, rfl, rfl⟩
  exact ⟨congrArg bytes hr.1, by simpa [ncodeunitsSubString, hr.2.2] using hn,
    by rw [hr.2.1, zero_val]⟩

theorem nestedSubstringConversion_proven : NestedSubstringConversion := by
  intro A S E convert assertType s parent error hc ha
  simp [convertSubString, hc, subStringWholeView, ha]

theorem substringConversionSemantics_proven : SubstringConversionSemantics :=
  ⟨substringConversions_proven, nestedSubstringConversion_proven⟩

theorem substringComparison_proven : SubstringComparison := by
  constructor
  · intro S sizeof memcmp bytes a b sizes laws
    simp only [equalStringViews, Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro ⟨hs, hm⟩
      exact (laws hs).mp hm
    · intro he
      have hs : (sizeof a).val = (sizeof b).val := by rw [sizes a, sizes b, he]
      exact ⟨hs, (laws hs).mpr he⟩
  · intro S memcmp sizeof cmpIndex a hm hc
    simp [cmpSubString, hm, hc]

theorem stringConversionCopiesView_proven : StringConversionCopiesView := by
  intro S Out E ops bytes outputBytes ss out laws h
  have hr : stringFromSubString ops ss = .ok out := by
    rcases h with h | h
    · exact h
    · simpa [stringSubString] using h
  have he : ops.unsafeString ss.string (ops.pointer ss.string (ss.offset + one)) ss.ncodeunits = .ok out := by
    simpa [stringFromSubString] using hr
  exact laws _ _ _ he

theorem wholeViewSemantics_proven : WholeViewSemantics := by
  intro S C CT E ops s len hn hl
  have hzero : zero + ops.ncodeunits s = ops.ncodeunits s := by
    apply Subtype.ext
    change wrapInt .i64 (zero.val + (ops.ncodeunits s).val) = _
    rw [zero_val, Int.zero_add]
    exact wrapInt_of_inRange _ _ (ops.ncodeunits s).property
  have hfirst : zero + one = one := by decide
  have hlen : lengthSubString ops (typedWholeSubString ops s) = .ok len := by
    simpa [lengthSubString, typedWholeSubString, hzero, hfirst] using hl
  refine ⟨hlen, typedWholeSubString ops s, ?_, hlen, rfl⟩
  have hz : one - one = zero := by decide
  simp [subStringWhole, rawSubstring, hz, typedWholeSubString]

theorem substringAllViewIntervals_proven : SubstringAllViewIntervals :=
  ⟨substringViewIntervalSemantics_proven, wholeViewSemantics_proven⟩



/-- Integer and range constructors select exactly the converted endpoint interval. -/
def ConvertedViewSpec : Prop :=
  ∀ {S C CT E I R : Type} (ops : SubStringOps S C CT E)
    (toInt : I → Except E Index) (range : RangeOps R I) (s : S) (a b : I)
    (r : R) (i j next : Index) (out : SubString S),
    toInt a = .ok i → toInt b = .ok j → range.first r = a → range.last r = b →
    1 ≤ i.val → i.val ≤ j.val → j.val < next.val →
    ops.checkboundsRange s i j = .ok () →
    ops.isvalid s i = .ok true → ops.isvalid s j = .ok true →
    ops.nextind s j = .ok next →
    (subStringInteger ops toInt s a b = .ok out ∨
      subStringRange ops range toInt s r = .ok out ∨
      viewString ops range toInt s r = .ok out ∨
      maybeviewRange ops range toInt s r = .ok out ∨
      getindexStringRange ops range toInt s r = .ok out) →
    out.string = s ∧ out.offset.val = i.val - 1 ∧
      0 < out.ncodeunits.val ∧ out.offset.val + out.ncodeunits.val = next.val - 1

theorem convertedView_proven : ConvertedViewSpec := by
  intro S C CT E I R ops toInt range s a b r i j next out ha hb hra hrb hi hij hjn hc hvi hvj hn h
  have htyped : typedSubString ops s i j = .ok out := by
    rcases h with h | h | h | h | h <;>
      simpa [subStringInteger, subStringRange, viewString, maybeviewRange,
        getindexStringRange, subStringInt, hra, hrb, ha, hb] using h
  exact (allViewConstructors_proven.1.1 ops s i j next out hi hij hjn hc hvi hvj hn htyped)

/-- Identity and regex-union conversions retain the same underlying string or view. -/
def ViewIdentitySpec : Prop :=
  (∀ {S : Type} (s : SubString S), convertSubStringIdentity s = s ∧
    cconvertUInt8 s = s ∧ cconvertInt8 s = s ∧ convertRegexSubString s = .substring s) ∧
  (∀ {S : Type} (s : S), convertRegexString s = .string s) ∧
  (∀ {A S E : Type} (convert : A → Except E S) (s : A) (out : S),
    convert s = .ok out → convertRegexAbstract convert s = .ok (.string out))

theorem viewIdentity_proven : ViewIdentitySpec := by
  refine ⟨?_, ?_, ?_⟩
  · intros; exact ⟨rfl, rfl, rfl, rfl⟩
  · intros; rfl
  · intro A S E convert s out h
    simp [convertRegexAbstract, h]

/-- Generic maybeview and string preserve successful indexing and String conversion results. -/
def ViewForwardingSpec : Prop :=
  (∀ {S A V E : Type} (get : S → A → Except E V) (s : S) (args : A) (out : V),
    get s args = .ok out → maybeviewArgs get s args = .ok out) ∧
  (∀ {S E : Type} (convert : S → Except E S) (s : S),
    convert s = .ok s → stringString convert s = .ok s) ∧
  (∀ {S : Type} (isAnnotated : Type → Bool) (s : SubString S),
    isannotatedSubString isAnnotated s = isAnnotated S) ∧
  (∀ {S C CT E : Type} (ops : SubStringOps S C CT E) (s : SubString S),
    codeunitTypeSubString ops s = ops.codeunitType s.string)

theorem viewForwarding_proven : ViewForwardingSpec := by
  exact ⟨by intros; assumption, by intros; assumption, by intros; rfl, by intros; rfl⟩

/-- String-index wrappers retain the index guarantees of the shared String helpers. -/
def ViewIndexWrapperSpec : Prop :=
  ∀ {S E : Type} (this next : SubString S → Index → Except E Index)
    (s : SubString S) (i start after : Index),
    this s i = .ok start → next s i = .ok after →
    thisindSubString this s i = .ok start ∧ nextindSubString next s i = .ok after ∧
    (∀ last, this s s.ncodeunits = .ok last → lastindexSubString this s = .ok last)

theorem viewIndexWrapper_proven : ViewIndexWrapperSpec := by
  intro S E this next s i start after ht hn
  exact ⟨ht, hn, fun _ h => h⟩

/-- Concrete substring ASCII classification sees exactly the view bytes. -/
def ViewAsciiSpec : Prop :=
  ∀ {S C CT E : Type} (ops : SubStringOps S C CT E)
    (bytes : SubString S → List UInt8) (s : SubString S),
    (∀ v, ops.isasciiCodeunits (JuliaLean.base.strings.basic.codeunits (fun _ => UInt8) v) =
      .ok ((bytes v).all (fun b => decide (b.toNat < 128)))) →
    isasciiSubString ops s = .ok ((bytes s).all (fun b => decide (b.toNat < 128)))

theorem viewAscii_proven : ViewAsciiSpec := by
  intro S C CT E ops bytes s h
  exact h s

/-- BitInteger repetition preserves the byte count of the general Integer method. -/
def BitIntegerRepeatSpec : Prop :=
  ∀ {S Out E I : Type} (ops : RepeatOps S Out E I) (s : S)
    (r : I) (count : Nat) (out : Out),
    RepeatInterface ops → ops.toUInt r = .ok count →
    repeatBitInteger ops s r = .ok out →
    ops.outputSize out = count * ops.sizeof (.string s)

theorem bitIntegerRepeat_proven : BitIntegerRepeatSpec := by
  intro S Out E I ops s r count out laws hc h
  apply repeatSize_proven ops (.string s) r count out laws hc
  simpa [repeatBitInteger] using h

/-- Both string argument unions concatenate the encoded arguments in order. -/
def StringUnionBuilderSpec : Prop :=
  (∀ {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (args : List (StringArg C S Sym)) (out : Out) (safe : Out → Prop),
    BuilderInterface ops safe →
    Int.ofNat (args.map ops.argumentBytes).flatten.length < IntTy.max .i64 →
    stringAny ops args = .ok out →
    ops.outputBytes out = (args.map ops.argumentBytes).flatten) ∧
  (∀ {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (args : List (RestrictedStringArg C S Sym)) (out : Out) (safe : Out → Prop),
    BuilderInterface ops safe →
    Int.ofNat ((args.map liftRestrictedStringArg).map ops.argumentBytes).flatten.length < IntTy.max .i64 →
    stringRestricted ops args = .ok out →
    ops.outputBytes out = ((args.map liftRestrictedStringArg).map ops.argumentBytes).flatten)

theorem stringUnionBuilder_proven : StringUnionBuilderSpec := by
  constructor
  · intro C S Sym Out E ops args out safe laws hb h
    exact (stringBuilderWritesInBounds_proven ops args out safe laws hb
      (by simpa [stringAny] using h)).1
  · intro C S Sym Out E ops args out safe laws hb h
    exact (stringBuilderWritesInBounds_proven ops (args.map liftRestrictedStringArg) out safe laws hb
      (by simpa [stringRestricted] using h)).1

/-- Interning uses the complete view byte span, including malformed UTF-8 bytes. -/
def ViewSymbolSpec : Prop :=
  ∀ {S Sym E : Type} (ops : PointerOps S)
    (convert : ops.Pointer → Except E ops.Pointer)
    (add : ops.Pointer → Index → Except E ops.Pointer)
    (size : SubString S → Index)
    (intern : SubString S → ops.Pointer → Index → Except E Sym)
    (viewBytes : SubString S → List UInt8) (symbolBytes : Sym → List UInt8)
    (s : SubString S) (out : Sym),
    (∀ view p symbol, intern view p (size view) = .ok symbol →
      symbolBytes symbol = viewBytes view) →
    symbolSubString ops convert add size intern s = .ok out →
    symbolBytes out = viewBytes s

theorem viewSymbol_proven : ViewSymbolSpec := by
  intro S Sym E ops convert add size intern viewBytes symbolBytes s out law h
  unfold symbolSubString at h
  cases hp : unsafeConvertSubString ops convert add (cconvertUInt8 s) with
  | error err => simp [hp] at h
  | ok p =>
    simp only [hp, bind, Except.bind] at h
    exact law s p out h


def entries : List Entry := [
  { id := "substring-converted-view-endpoints", juliaFile := "base/strings/substring.jl"
    juliaFns := ["SubString(s::AbstractString, i::Integer, j::Integer=lastindex(s))", "SubString(s::AbstractString, r::AbstractUnitRange{<:Integer})", "view(s::AbstractString, r::AbstractUnitRange{<:Integer})", "maybeview(s::AbstractString, r::AbstractUnitRange{<:Integer})", "getindex(s::AbstractString, r::AbstractUnitRange{<:Integer})"]
    statement := "Integer and range constructors preserve the parent and select exactly the converted endpoint interval."
    source := "base/strings/substring.jl:109,110,120,121,322", status := .proven, prop := ``ConvertedViewSpec, thm := some ``convertedView_proven },
  { id := "substring-identity-wrappers", juliaFile := "base/strings/substring.jl"
    juliaFns := ["convert(::Type{T}, s::T) where {T<:SubString}", "convert(::Type{Union{String, SubString{String}}}, s::String)", "convert(::Type{Union{String, SubString{String}}}, s::SubString{String})", "convert(::Type{Union{String, SubString{String}}}, s::AbstractString)", "cconvert(::Type{Ptr{UInt8}}, s::SubString{String})", "cconvert(::Type{Ptr{Int8}}, s::SubString{String})"]
    statement := "Same-type, regex-union and C-call conversions preserve the underlying string or substring."
    source := "base/strings/substring.jl:126,129,130,131,193,194", status := .proven, prop := ``ViewIdentitySpec, thm := some ``viewIdentity_proven },
  { id := "substring-forwarding-wrappers", juliaFile := "base/strings/substring.jl"
    juliaFns := ["maybeview(s::AbstractString, args...)", "codeunit(s::SubString)", "_isannotated(::SubString{T}) where {T}", "string(a::String)"]
    statement := "Indexing and conversion wrappers preserve their results, annotation classification and parent code-unit type."
    source := "base/strings/substring.jl:122,140,206,208", status := .proven, prop := ``ViewForwardingSpec, thm := some ``viewForwarding_proven },
  { id := "substring-index-wrappers", juliaFile := "base/strings/substring.jl"
    juliaFns := ["thisind(s::SubString{String}, i::Int)", "nextind(s::SubString{String}, i::Int)", "lastindex(s::SubString{String})"]
    statement := "Substring index wrappers preserve the shared String helpers character-boundary results."
    source := "base/strings/substring.jl:174,175,178", status := .proven, prop := ``ViewIndexWrapperSpec, thm := some ``viewIndexWrapper_proven },
  { id := "substring-ascii-wrapper", juliaFile := "base/strings/substring.jl"
    juliaFns := ["isascii(ss::SubString{String})"]
    statement := "Substring ASCII classification examines exactly the view bytes."
    source := "base/strings/substring.jl:166", status := .proven, prop := ``ViewAsciiSpec, thm := some ``viewAscii_proven },
  { id := "substring-symbol-bytes", juliaFile := "base/strings/substring.jl"
    juliaFns := ["Symbol(s::SubString{String})"]
    statement := "Interning a substring preserves its complete byte span, including malformed UTF-8 bytes."
    source := "base/strings/substring.jl:211", status := .proven, prop := ``ViewSymbolSpec, thm := some ``viewSymbol_proven },
  { id := "substring-byte-builder", juliaFile := "base/strings/substring.jl"
    juliaFns := ["__unsafe_string!(out, s::String, offs::Integer)", "__unsafe_string!(out, s::SubString{String}, offs::Integer)", "__unsafe_string!(out, s::Symbol, offs::Integer)", "_string(a::Union{Char, String, SubString{String}, Symbol}...)"]
    statement := "The string builder copies the complete encoded arguments in order, with the exact output byte count."
    source := "base/strings/substring.jl:233,239,245,256", status := .proven, prop := ``StringBuilderWritesInBounds, thm := some ``stringBuilderWritesInBounds_proven },
  { id := "substring-string-union-builders", juliaFile := "base/strings/substring.jl"
    juliaFns := ["string(a::Union{Char, String, Symbol}...)", "string(a::Union{Char, String, SubString{String}, Symbol}...)"]
    statement := "Both supported argument unions concatenate the encoded argument bytes in order."
    source := "base/strings/substring.jl:252,254", status := .proven, prop := ``StringUnionBuilderSpec, thm := some ``stringUnionBuilder_proven },
  { id := "substring-bitinteger-repeat", juliaFile := "base/strings/substring.jl"
    juliaFns := ["repeat(s::String, r::BitInteger)"]
    statement := "Successful BitInteger repetition returns exactly count times the source byte length."
    source := "base/strings/substring.jl:287", status := .proven, prop := ``BitIntegerRepeatSpec, thm := some ``bitIntegerRepeat_proven },

  { id := "strings-repeat-size", juliaFile := "base/strings/substring.jl"
    juliaFns := ["repeat(::String, ::Integer)", "repeat(::Union{String,SubString{String}}, ::Integer)"]
    statement := "Successful string repetition returns exactly the requested number of source bytes, without a wrapped allocation size."
    source := "invariant"
    status := .proven, prop := ``RepeatSize, thm := some ``repeatSize_proven },
  { id := "strings-raw-substring-iterate", juliaFile := "base/strings/substring.jl"
    juliaFns := ["raw_substring(::AbstractString, ::Int, ::Int)", "iterate(::SubString, ::Integer)"]
    statement := "Iteration yields exactly the parent characters inside a character-aligned byte view. Truncated endpoints permit StringIndexError, but never a different exception, wrong character, or character extending outside the view."
    source := "base/strings/substring.jl:11-16: truncated characters are well-defined; accessing characters truncated by SubString may throw StringIndexError"
    status := .refuted, prop := ``RawSubstringIterates, thm := some ``rawSubstringIterates_refuted
    issue := "existing runtime reproducer; see bugs/strings-raw-substring-iterate.yaml" },
  { id := "memsafety-strings-substring-index", juliaFile := "base/strings/substring.jl"
    juliaFns := ["SubString", "codeunit(::SubString)", "getindex(::SubString)", "isvalid(::SubString)"]
    statement := "Constructors check the parent endpoints, and every SubString operation checks its local index before adding the stored in-parent offset."
    source := "base/strings/substring.jl:71-171; base/strings/string.jl:252-271"
    status := .proven, prop := ``SubstringIndexInBounds, thm := some ``substringIndexInBounds_proven },
  { id := "stringscova-substring-empty-offset", juliaFile := "base/strings/substring.jl"
    juliaFns := ["SubString{T}(::T,::Int,::Int)"]
    statement := "An empty SubString preserves the requested insertion offset, so its stored offset is first minus one."
    source := "base/strings/substring.jl:76-84"
    status := .refuted, prop := ``EmptySubstringOffset, thm := some ``emptySubstringOffset_refuted
    issue := "#52877" },
  { id := "stringscova-sub-parentindices-rebuilt", juliaFile := "base/strings/substring.jl"
    juliaFns := ["parentindices(::SubString)"]
    statement := "Parent indices begin at the mathematical parent byte position of the view and end at a nonnegative character start no later than the final view byte."
    source := "base/strings/substring.jl:181"
    status := .proven, prop := ``ParentIndices, thm := some ``parentIndices_proven },
  { id := "substring-view-construction", juliaFile := "base/strings/substring.jl"
    juliaFns := ["SubString{T}(::T,::Int,::Int)", "SubString(::SubString,::Int,::Int)"]
    statement := "A successful nonempty substring constructor preserves its parent and selects the requested parent range."
    source := "base/strings/substring.jl:49-69,76-84,108-122,322"
    status := .proven, prop := ``AllViewConstructors, thm := some ``allViewConstructors_proven },
  { id := "substring-raw-parent-span", juliaFile := "base/strings/substring.jl"
    juliaFns := ["raw_substring(::AbstractString,::Int,::Int)", "raw_substring(::SubString,::Int,::Int)"]
    statement := "Every successful raw substring has a nonnegative byte span within its parent."
    source := "base/strings/substring.jl:7-16,86-98"
    status := .proven, prop := ``RawSubstringAllWithinParent, thm := some ``rawSubstringAllWithinParent_proven },
  { id := "substring-indexed-parent-reads", juliaFile := "base/strings/substring.jl"
    juliaFns := ["codeunit(::SubString,::Integer)", "getindex(::SubString,::Integer)", "isvalid(::SubString,::Integer)"]
    statement := "A checked local read uses the corresponding parent index, and an out-of-view validity check returns false without reading the parent."
    source := "base/strings/substring.jl:146-172"
    status := .proven, prop := ``SubstringIndexInBounds, thm := some ``substringIndexInBounds_proven },
  { id := "substring-view-interval", juliaFile := "base/strings/substring.jl"
    juliaFns := ["SubString{T}(::T)", "SubString(::AbstractString)", "length(::SubString)", "length(::SubString{String})"]
    statement := "View lengths count exactly the parent character starts within the view interval; whole views preserve the parent's character length."
    source := "base/strings/substring.jl:103-105,117,141-144"
    status := .proven, prop := ``SubstringAllViewIntervals, thm := some ``substringAllViewIntervals_proven },
  { id := "substring-pointer-offset", juliaFile := "base/strings/substring.jl"
    juliaFns := ["pointer(::SubString{String})", "pointer(::SubString{String},::Integer)", "unsafe_convert(::Type{Ptr{R}},::SubString{String})", "hash(::SubString{String},::UInt)"]
    statement := "Pointers translate view-relative positions to parent byte addresses, and equal byte content has equal hashes for the same seed."
    source := "base/strings/substring.jl:193-213"
    status := .proven, prop := ``SubstringPointerUsesParentOffset, thm := some ``substringPointerUsesParentOffset_proven },
  { id := "substring-comparison", juliaFile := "base/strings/substring.jl"
    juliaFns := ["==(::Union{String,SubString{String}},::Union{String,SubString{String}})", "cmp(::SubString{String},::SubString{String})"]
    statement := "String-view equality agrees with equality of the full byte sequences, and comparing a view with itself returns zero."
    source := "base/strings/substring.jl:183-190"
    status := .proven, prop := ``SubstringComparison, thm := some ``substringComparison_proven },
  { id := "substring-string-copy", juliaFile := "base/strings/substring.jl"
    juliaFns := ["String(::SubString{String})", "string(::SubString{String})"]
    statement := "Converting a substring to String copies exactly its stored byte span from the parent."
    source := "base/strings/substring.jl:133-137,209"
    status := .proven, prop := ``StringConversionCopiesView, thm := some ``stringConversionCopiesView_proven },
  { id := "substring-filter-order", juliaFile := "base/strings/substring.jl"
    juliaFns := ["filter(::Any,::Union{String,SubString{String}})"]
    statement := "Filtering retains exactly the accepted characters in their original order."
    source := "base/strings/substring.jl:309-320"
    status := .proven, prop := ``FilterKeepsAcceptedCharacters, thm := some ``filterKeepsAcceptedCharacters_proven },
  { id := "substring-conversions", juliaFile := "base/strings/substring.jl"
    juliaFns := ["convert(::Type{SubString{S}},::AbstractString)"]
    statement := "Conversion calls the unparameterized SubString constructor, preserves whole-view bytes when the result has the required type, and rejects a nested-view result when the result type assertion fails."
    source := "base/strings/substring.jl:124-131"
    status := .proven, prop := ``SubstringConversionSemantics, thm := some ``substringConversionSemantics_proven },
]

end JuliaLean.Proofs.base.strings.substring
