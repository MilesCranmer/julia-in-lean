import JuliaLean.base.array
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int

/-!
# Properties of `base/array.jl`

These statements refer only to the source-mirrored definitions in `JuliaLean.base.array`.
The search specifications use the ordered finite sequence returned by a collection's `pairs`.
Layout fields and their well-formedness are the runtime invariants of concrete Julia types.
-/

namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000


/-- A search returns a matching key, with no earlier matching element. -/
def firstMatch (test : α → Bool) (pairs : List (K × α)) (key : K) : Prop :=
  ∃ before value after, pairs = before ++ (key, value) :: after ∧
    test value = true ∧ ∀ p ∈ before, test p.2 = false

/-- A backward search returns a matching key, with no later matching element. -/
def lastMatch (test : α → Bool) (pairs : List (K × α)) (key : K) : Prop :=
  ∃ before value after, pairs = before ++ (key, value) :: after ∧
    test value = true ∧ ∀ p ∈ after, test p.2 = false

theorem findfirst_nil (test : α → Bool) :
    findfirst (m := Id) test ([] : List (K × α)) = none := by
  simp [findfirst, Bind.bind, Pure.pure]

theorem findfirst_cons (test : α → Bool) (k : K) (a : α) (pairs : List (K × α)) :
    findfirst (m := Id) test ((k, a) :: pairs) =
      (if test a then some k else findfirst (m := Id) test pairs) := by
  cases ht : test a <;> simp [findfirst, ht, Bind.bind, Pure.pure]

theorem findfirst_firstMatch (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findfirst (m := Id) test pairs = some key) : firstMatch test pairs key := by
  induction pairs with
  | nil =>
    rw [findfirst_nil] at h
    cases h
  | cons p pairs ih =>
    obtain ⟨k, a⟩ := p
    rw [findfirst_cons] at h
    cases ht : test a with
    | true =>
      simp [ht] at h
      have hk := Option.some.inj h
      subst k
      exact ⟨[], a, pairs, rfl, ht, by simp⟩
    | false =>
      simp [ht] at h
      obtain ⟨before, value, after, he, hv, hb⟩ := ih h
      refine ⟨(k, a) :: before, value, after, ?_, hv, ?_⟩
      · simp [he]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ht
        · exact hb p hp

theorem findfirst_none_iff (test : α → Bool) (pairs : List (K × α)) :
    findfirst (m := Id) test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false := by
  induction pairs with
  | nil => simp [findfirst_nil]
  | cons p pairs ih =>
    obtain ⟨k, a⟩ := p
    rw [findfirst_cons]
    cases ht : test a <;> simp [ht, ih]

theorem findfirst_sound (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findfirst (m := Id) test pairs = some key) :
    ∃ value, (key, value) ∈ pairs ∧ test value = true := by
  obtain ⟨before, value, after, he, hv, _⟩ := findfirst_firstMatch test pairs key h
  exact ⟨value, by simp [he], hv⟩

theorem findlast_lastMatch (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findlast (m := Id) List.reverse test pairs = some key) : lastMatch test pairs key := by
  obtain ⟨before, value, after, he, hv, hb⟩ :=
    findfirst_firstMatch test pairs.reverse key h
  refine ⟨after.reverse, value, before.reverse, ?_, hv, ?_⟩
  · have := congrArg List.reverse he
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using this
  · intro p hp
    exact hb p (by simpa using hp)

theorem findlast_sound (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findlast (m := Id) List.reverse test pairs = some key) :
    ∃ value, (key, value) ∈ pairs ∧ test value = true := by
  obtain ⟨before, value, after, he, hv, _⟩ := findlast_lastMatch test pairs key h
  exact ⟨value, by simp [he], hv⟩

def FirstSearchSound : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findfirst (m := Id) test pairs = some key → ∃ value, (key, value) ∈ pairs ∧ test value = true

def FirstSearchComplete : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)),
  findfirst (m := Id) test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false

def FirstSearchEarliest : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findfirst (m := Id) test pairs = some key → firstMatch test pairs key

def LastSearchSound : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findlast (m := Id) List.reverse test pairs = some key → ∃ value, (key, value) ∈ pairs ∧ test value = true

def LastSearchLatest : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findlast (m := Id) List.reverse test pairs = some key → lastMatch test pairs key

theorem firstSearchSound : FirstSearchSound := fun _ _ => findfirst_sound
theorem firstSearchComplete : FirstSearchComplete := fun _ _ => findfirst_none_iff
theorem firstSearchEarliest : FirstSearchEarliest := fun _ _ => findfirst_firstMatch
theorem lastSearchSound : LastSearchSound := fun _ _ => findlast_sound
theorem lastSearchLatest : LastSearchLatest := fun _ _ => findlast_lastMatch

/-- The complete documented isbitsunion contract, including every union cardinality. -/
def IsBitsUnionDocumented : Prop :=
  (∀ ms : List Layout, 2 ≤ ms.length → (ms.map Layout.name).Nodup → (∀ d ∈ ms, d.WF) →
    (isbitsunion unionType storedInline (.union ms) = true ↔ ∀ d ∈ ms, d.isbits = true) ∧
      allocatedinline storedInline (.union ms) = isbitsunion unionType storedInline (.union ms)) ∧
  (∀ t : StoredType, (∀ ms, t ≠ .union ms) → isbitsunion unionType storedInline t = false) ∧
  (∀ d : Layout, d.WF → d.isbits = true → allocatedinline storedInline (.dt d) = true) ∧
  (∀ d : Layout, d.mayInline = false → allocatedinline storedInline (.dt d) = false) ∧
  allocatedinline storedInline .any = false ∧ allocatedinline storedInline .bottom = false ∧
    ∀ n, allocatedinline storedInline (.abstractDT n) = false

def valTypes : List Layout := (List.range 127).map fun i => ⟨i, true, true, false, false, 0, 1⟩

theorem isBitsUnionDocumented_refuted : ¬ IsBitsUnionDocumented := by
  intro h
  have hn : (valTypes.map Layout.name).Nodup := by
    simp [valTypes, List.map_map, Function.comp_def, List.nodup_range]
  have hwf : ∀ d ∈ valTypes, d.WF := by
    intro d hd
    simp only [valTypes, List.mem_map] at hd
    obtain ⟨i, _, rfl⟩ := hd
    exact ⟨rfl, ⟨0, rfl⟩, Nat.dvd_zero 1⟩
  have hb : ∀ d ∈ valTypes, d.isbits = true := by
    intro d hd
    simp only [valTypes, List.mem_map] at hd
    obtain ⟨i, _, rfl⟩ := hd
    rfl
  have hh := ((h.1 valTypes (by simp [valTypes]) hn hwf).1).2 hb
  have hall : valTypes.all (fun d => inlineAlloc d true) = true := by simp [valTypes, inlineAlloc]
  have hl : valTypes.length = 127 := by simp [valTypes]
  have hz : isbitsunion unionType storedInline (.union valTypes) = false := by
    simp [isbitsunion, unionType, allocatedinline, storedInline, unionInlineCount, hall, hl,
      JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
  rw [hz] at hh
  contradiction

/-- The documented isbits-union test is correct below the runtime member-count limit. -/
def IsBitsUnionSmall : Prop := ∀ ms : List Layout,
  2 ≤ ms.length → ms.length < 127 → (∀ d ∈ ms, d.WF) →
    (isbitsunion unionType storedInline (.union ms) = true ↔ ∀ d ∈ ms, d.isbits = true)

theorem isBitsUnionSmall : IsBitsUnionSmall := by
  intro ms hlow hhigh hwf
  have heq : ∀ d ∈ ms, inlineAlloc d true = d.isbits := by
    intro d hd
    simpa [inlineAlloc] using (hwf d hd).1.symm
  by_cases hall : ms.all (fun d => inlineAlloc d true) = true
  · have hb : ∀ d ∈ ms, d.isbits = true := by
      intro d hd
      rw [← heq d hd]
      exact List.all_eq_true.mp hall d hd
    have htest : isbitsunion unionType storedInline (.union ms) = true := by
      simp [isbitsunion, unionType, allocatedinline, storedInline, unionInlineCount, hall,
        show 0 < ms.length by omega, hhigh, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
    exact ⟨fun _ => hb, fun _ => htest⟩
  · have hfalse : ms.all (fun d => inlineAlloc d true) = false := by
      cases h : ms.all (fun d => inlineAlloc d true) <;> simp_all
    have htest : isbitsunion unionType storedInline (.union ms) = false := by
      simp [isbitsunion, unionType, allocatedinline, storedInline, unionInlineCount, hfalse,
        JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
    constructor
    · intro h
      rw [htest] at h
      contradiction
    · intro hb
      apply False.elim
      apply hall
      apply List.all_eq_true.mpr
      intro d hd
      rw [heq d hd]
      exact hb d hd

/-- Independent specification: the first matching one-based index at least `start`. -/
def firstAtLeast (test : α → Bool) (xs : List α) (start : Int) : Option Int :=
  ((xs.zipIdx 1).find? (fun p => test p.1 && decide (start ≤ (p.2 : Int)))).map
    (fun p => (p.2 : Int))

/-- Independent specification: the last matching one-based index at most `start`. -/
def lastUpTo (test : α → Bool) (xs : List α) (start : Int) : Option Int :=
  ((xs.zipIdx 1).reverse.find? (fun p => test p.1 && decide ((p.2 : Int) ≤ start))).map
    (fun p => (p.2 : Int))

/-- The original full all-starts promise, including starts beyond either array boundary. -/
def FindAllStarts : Prop :=
  ∀ (α : Type) (t : IntTy) (test : α → Bool) (xs : List α) (i : JInt t)
    (hn : xs.length < 2 ^ 62), IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max →
    (findnext (fun _ => one) (fun _ => JInt.wrap .i64 xs.length)
      (fun _ j => indexConvert j) (fun j k => decide (j.val > k.val))
      vectorGet (fun a => .ok (test a)) (forwardRank xs.length)
      (nextVectorIndex xs.length hn) xs i).map (Option.map Subtype.val) = .ok (firstAtLeast test xs i.val) ∧
    (findprev (fun _ => one) (fun _ j => indexConvert j) (fun j k => decide (j.val < k.val))
      vectorGet (fun a => .ok (test a)) backwardRank prevVectorIndex xs i).map (Option.map Subtype.val) = .ok (lastUpTo test xs i.val)

theorem findAllStarts_refuted : ¬ FindAllStarts := by
  intro h
  have hn : ([1, 2] : List Int).length < 2 ^ 62 := by decide
  have bad := (h Int .i64 (fun x => x % 2 == 0) [1, 2] zero hn (by decide) (by decide)).1
  have expected : firstAtLeast (fun x : Int => x % 2 == 0) [1, 2] zero.val = some 2 := by decide
  have actual : (findnext (fun _ => one) (fun _ => JInt.wrap .i64 ([1, 2] : List Int).length)
      (fun _ j => indexConvert j) (fun j k => decide (j.val > k.val))
      vectorGet (fun a => .ok (a % 2 == 0)) (forwardRank ([1, 2] : List Int).length)
      (nextVectorIndex ([1, 2] : List Int).length hn) ([1, 2] : List Int) zero) = .error .bounds := by
    change findnext.loop vectorGet (fun a : Int => Except.ok (a % 2 == 0))
      (forwardRank 2) (nextVectorIndex 2 hn) ([1, 2] : List Int) (JInt.wrap .i64 2) zero =
        Except.error Error.bounds
    delta findnext.loop
    rw [WellFounded.Nat.fix_eq]
    simp [vectorGet, zero, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits,
      Bind.bind, Except.bind]
  rw [actual, expected] at bad
  cases bad

/-- A matching integer in a range has a positive key. The endpoint, searched
value, step, subtraction, remainder and quotient types are independent, as in
Julia's generic methods. Arithmetic callees remain typed interfaces; the
counterexample below instantiates them with ordinary Int8 arithmetic. -/
def RangeFindfirstPositive : Prop :=
  (∀ (V X Diff : Type) (value : V → Int) (xValue : X → Int)
    (subtract : X → V → Diff) (convertDifference : Diff → Except Error I)
    (lo hi : V) (x : X),
    value lo ≤ xValue x → xValue x ≤ value hi →
    ∃ k : I,
      findfirstUnitRange (m := Except Error)
        (fun r : V × V => r.1) Prod.snd value xValue
        (fun _ => .ok one) subtract (fun _ => convertDifference) (· + ·)
        x (lo, hi) = .ok (some k) ∧ 1 ≤ k.val) ∧
  (∀ (V X Step Diff Rem Quot : Type)
    (value : V → Int) (xValue : X → Int) (stepValue : Step → Int)
    (subtract : X → V → Diff) (remainder : Diff → Step → Except Error Rem)
    (iszero : Rem → Bool) (divide : Diff → Step → Except Error Quot)
    (plusOne : Quot → Quot) (convertKey : Quot → Except Error I)
    (lo hi : V) (step : Step) (x : X),
    stepValue step ≠ 0 →
    min (value lo) (value hi) ≤ xValue x →
    xValue x ≤ max (value lo) (value hi) →
    (∃ n : Nat, xValue x = value lo + n * stepValue step) →
    ∃ k : I,
      findfirstStepRange (m := Except Error)
        (fun r : V × Step × V =>
          if 0 < stepValue r.2.1 then decide (value r.2.2 < value r.1)
          else decide (value r.1 < value r.2.2))
        (fun r => if value r.1 ≤ value r.2.2 then r.1 else r.2.2)
        (fun r => if value r.1 ≤ value r.2.2 then r.2.2 else r.1)
        (fun r => r.1) (fun r => r.2.1)
        (fun a b => decide (value a ≤ xValue b))
        (fun a b => decide (xValue a ≤ value b))
        subtract remainder iszero divide plusOne convertKey x (lo, step, hi) =
          .ok (some k) ∧ 1 ≤ k.val)

theorem rangeFindfirstPositive_refuted : ¬ RangeFindfirstPositive := by
  intro h
  obtain ⟨k, hk, hp⟩ := h.2 (JInt .i8) (JInt .i8) (JInt .i8)
    (JInt .i8) (JInt .i8) (JInt .i8)
    Subtype.val Subtype.val Subtype.val (· - ·)
    (fun a b => .ok (JInt.wrap .i8 (a.val.tmod b.val)))
    (fun a => a.val == 0)
    (fun a b => .ok (JInt.wrap .i8 (a.val.tdiv b.val)))
    (fun a => a + JInt.wrap .i8 1) indexConvert
    (JInt.wrap .i8 (-100)) (JInt.wrap .i8 120) (JInt.wrap .i8 2) (JInt.wrap .i8 100)
    (by decide) (by decide) (by decide) ⟨100, by decide⟩
  have actual :
      findfirstStepRange (m := Except Error)
        (fun r : JInt .i8 × JInt .i8 × JInt .i8 =>
          if 0 < r.2.1.val then decide (r.2.2.val < r.1.val)
          else decide (r.1.val < r.2.2.val))
        (fun r => if r.1.val ≤ r.2.2.val then r.1 else r.2.2)
        (fun r => if r.1.val ≤ r.2.2.val then r.2.2 else r.1)
        (fun r => r.1) (fun r => r.2.1)
        (fun a b => decide (a.val ≤ b.val)) (fun a b => decide (a.val ≤ b.val)) (· - ·)
        (fun a b => .ok (JInt.wrap .i8 (a.val.tmod b.val)))
        (fun a => a.val == 0)
        (fun a b => .ok (JInt.wrap .i8 (a.val.tdiv b.val)))
        (fun a => a + JInt.wrap .i8 1) indexConvert (JInt.wrap .i8 100)
        (JInt.wrap .i8 (-100), JInt.wrap .i8 2, JInt.wrap .i8 120) =
          .ok (some (JInt.wrap .i64 (-27))) := by rfl
  rw [actual] at hk
  cases hk
  exact (by decide : ¬ (1 ≤ (JInt.wrap .i64 (-27)).val)) hp

/-- Out-of-place reversal and in-place reversal of a copy have equal results
or the same exception, including empty and one-element windows. -/
def ReverseCopyAgrees : Prop :=
  ∀ (α : Type) (s t : IntTy) (xs : List α) (start : JInt s) (stop : JInt t),
    xs.length < 2 ^ 62 →
    ((JuliaLean.base.array.reverse (m := VectorM α)
      (fun i => liftM (indexConvert i)) (fun i => liftM (indexConvert i))
      heapSimilar (fun _ => pure one) heapLength heapGet heapSet 0 start stop).run
        [xs.map some]).map (fun (handle, heap) => heap[handle]?) =
    ((reverseBang (m := VectorM α)
      (fun i => liftM (indexConvert i)) (fun i => liftM (indexConvert i))
      (fun _ => pure one) heapLength
      (fun lo hi => pure (midpoint (· + ·) (· - ·)
        (fun x n => JInt.wrap .i64 ((x.val % 2 ^ 64) / 2 ^ n.val.toNat)) lo hi))
      heapGet heapSet 0 start stop).run [xs.map some]).map
        (fun (handle, heap) => heap[handle]?)

theorem reverseCopyAgrees_refuted : ¬ ReverseCopyAgrees := by
  intro h
  have bad := h Int .i64 .i64 [1, 2, 3] (JInt.wrap .i64 5) (JInt.wrap .i64 5) (by decide)
  have actual : ((JuliaLean.base.array.reverse (m := VectorM Int)
      (fun i : I => liftM (indexConvert i)) (fun i : I => liftM (indexConvert i))
      heapSimilar (fun _ => pure one) heapLength heapGet heapSet 0
        (JInt.wrap .i64 5) (JInt.wrap .i64 5)).run
        [([1, 2, 3] : List Int).map some]) = .error .bounds := by rfl
  rw [actual] at bad
  have success : ((reverseBang (m := VectorM Int)
      (fun i : I => liftM (indexConvert i)) (fun i : I => liftM (indexConvert i))
      (fun _ => pure one) heapLength
      (fun lo hi => pure (midpoint (· + ·) (· - ·)
        (fun x n => JInt.wrap .i64 ((x.val % 2 ^ 64) / 2 ^ n.val.toNat)) lo hi))
      heapGet heapSet 0 (JInt.wrap .i64 5) (JInt.wrap .i64 5)).run
        [([1, 2, 3] : List Int).map some]) =
      .ok (0, [[some 1, some 2, some 3]]) := by rfl
  rw [success] at bad
  cases bad

/-- Every Int-representable nonnegative Integer length fitting in Memory is
accepted. `nativeInt` distinguishes Julia Int from every other Integer subtype
when dispatching `_wrap` on the unconverted singleton tuple. -/
def WrapMemoryIntegerSpec : Prop :=
  ∀ (nativeInt : Bool) (len capacity : Nat),
    len ≤ capacity → capacity < 2 ^ 63 →
    wrapMemoryLength (m := Except Error)
      (fun n : Nat => .ok (JInt.wrap .i64 n))
      (fun cap : Nat => .ok (JInt.wrap .i64 cap, one))
      (fun ref dims =>
        if nativeInt then
          wrapCheck Prod.fst id Prod.snd
            (fun ds => .ok (JInt.wrap .i64 (ds.foldl (fun n d => n * d.val) 1)))
            ref (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int)))
        else .error (.method "_wrap"))
      (fun _ dims => .ok dims) capacity len = .ok [JInt.wrap .i64 len]

theorem wrapMemoryIntegerSpec_refuted : ¬ WrapMemoryIntegerSpec := by
  intro h
  have bad := h false 2 3 (by decide) (by decide)
  change Except.error (Error.method "_wrap") = Except.ok [JInt.wrap .i64 2] at bad
  cases bad

/-- Observable result of wrapping memory: the original reference and dimensions. -/
abbrev Wrapped (α : Type) := (List (Option α) × I) × List I

def wrapContract (operation : List Int → Except Error (Wrapped α))
    (memory : List (Option α)) (offset : I) : Prop :=
  (∀ dims, (∀ d ∈ dims, IntTy.i64.min ≤ d ∧ d ≤ IntTy.i64.max) →
    (∃ d ∈ dims, d < 0) →
    ∃ message, operation dims = .error (.argument message)) ∧
  (∀ dims, (∀ d ∈ dims, 0 ≤ d ∧ d < IntTy.i64.max) →
    dims.foldr (· * ·) 1 ≤ IntTy.i64.max →
    (dims.foldr (· * ·) 1 ≤ (memory.length : Int) + 1 - offset.val →
      operation dims = .ok ((memory, offset), dims.map (JInt.wrap .i64))) ∧
    ((memory.length : Int) + 1 - offset.val < dims.foldr (· * ·) 1 →
      ∃ message, operation dims = .error (.dimensionMismatch message))) ∧
  (∀ dims, (∃ d ∈ dims, d < IntTy.i64.min ∨ IntTy.i64.max < d) →
    operation dims = .error .inexact)

/-- The complete old wrap contract, for tuple dimensions, scalar dimensions,
MemoryRef and Memory, including aliasing and conversion errors.
The singleton law is the external Core.checked_dims method in boot.jl:813. -/
def WrapDocumented : Prop :=
  ∀ (checkedDims : List I → Except Error I),
    (∀ d, checkedDims [d] = .ok d) →
    ∀ (α : Type) (memory : List (Option α)) (offset : I),
      memory.length < 2 ^ 63 → 1 ≤ offset.val → offset.val ≤ (memory.length : Int) + 1 →
      let toInt := fun n : Int => (JInt.convert .i64 n).mapError (fun _ => Error.inexact)
      let check := wrapCheck Prod.fst (fun mem : List (Option α) => JInt.wrap .i64 mem.length)
        Prod.snd checkedDims
      let newArray := fun ref dims => Except.ok (ref, dims)
      wrapContract
        (wrapRefDims (fun ds => ds.mapM toInt) check newArray (memory, offset)) memory offset ∧
      wrapContract
        (wrapMemoryDims (fun ds => ds.mapM toInt) (fun mem => .ok (mem, one))
          check newArray memory) memory one ∧
      wrapContract
        (fun ds => match ds with
          | [l] => wrapRefLength toInt check newArray (memory, offset) l
          | _ => .error (.method "wrap")) memory offset ∧
      wrapContract
        (fun ds => match ds with
          | [l] => wrapMemoryLength toInt (fun mem => .ok (mem, one))
              (fun ref ds => check ref (ds.map (JInt.wrap .i64))) newArray memory l
          | _ => .error (.method "wrap")) memory one ∧
      wrapMemory (fun mem => Except.ok (mem, one))
        (fun mem => JInt.wrap .i64 mem.length) newArray memory =
          .ok ((memory, one), [JInt.wrap .i64 memory.length])

theorem wrapDocumented_refuted : ¬ WrapDocumented := by
  intro h
  let check : List I → Except Error I := fun ds =>
    .ok (ds.foldr (· * ·) one)
  have single : ∀ d, check [d] = .ok d := by
    intro d
    dsimp [check]
    congr 1
    apply Subtype.ext
    change wrapInt .i64 (d.val * one.val) = d.val
    rw [show one.val = 1 from rfl, Int.mul_one]
    exact wrapInt_of_inRange .i64 d.val d.property
  have hc := h check single Unit [none, none, none] one (by decide) (by decide) (by decide)
  obtain ⟨message, bad⟩ := hc.2.2.1.1 [-1]
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        subst d; decide)
    ⟨-1, by simp, by decide⟩
  have actual :
      wrapRefLength (m := Except Error)
        (fun n : Int => (JInt.convert .i64 n).mapError (fun _ => Error.inexact))
        (wrapCheck Prod.fst (fun mem : List (Option Unit) => JInt.wrap .i64 mem.length)
          Prod.snd check)
        (fun ref dims => .ok (ref, dims))
        ([none, none, none], one) (-1) =
        .ok (([none, none, none], one), [JInt.wrap .i64 (-1)]) := by rfl
  change (wrapRefLength (m := Except Error) _ _ _ _ (-1) : Except Error (Wrapped Unit)) =
    Except.error (.argument message) at bad
  rw [actual] at bad
  cases bad

/-- The specialised membership search must use the same equality as membership
in the original collection, including IEEE signed zeros and NaNs. -/
def TupleMembershipAgreement : Prop :=
  ∀ (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) (initial : MutableMemory I),
    let operation := findallIn2962 (m := MutationM I)
      (fun xs ys => findin (fun values => pure values)
        (findinSet (mutableAllocate 0 zero)
          (fun values => (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1)))
          (fun x values => pure (values.any (JuliaLean.C.jlFpiseq x)))
          mutablePush) xs ys) ys xs
    let result := operation.run initial
    result.1.map (fun handle => result.2.contents handle) =
      .ok (((xs.zipIdx 1).filter (fun p => ys.any (JuliaLean.C.jlEqFloat p.1))).map
        (fun p => some (JInt.wrap .i64 (p.2 : Int))))

theorem tupleMembershipAgreement_refuted : ¬ TupleMembershipAgreement := by
  intro h
  have bad := h [JuliaLean.Promotion.Fl.zero true] [JuliaLean.Promotion.Fl.zero false] ⟨[], []⟩
  change (Except.ok [] : Except Error (List (Option I))) = .ok [some one] at bad
  cases bad

/-- Hash-based indexin must report first membership indices under the equality
used by collection membership. -/
def IndexinMembershipAgreement : Prop :=
  ∀ (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) (initial : MutableMemory (Option I)),
    let operation := indexin
      (m := StateT (List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double × I))
        (MutationM (Option I)))
      (fun values => (List.range values.length).map (fun (i : Nat) => JInt.wrap .i64 ((i : Int) + 1)))
      (pure ()) List.zip
      (fun _ value key => dictInsertFirst JuliaLean.C.jlFpiseq value key)
      (fun _ value default => dictGet JuliaLean.C.jlFpiseq value default)
      (typedLiteral (fun n => liftM (mutableAllocate (α := Option I) 0 n))
        (fun a value i => liftM (mutableTypedSet (α := Option I) a value i)) true) xs ys
    let result := (operation.run []).run initial
    result.1.map (fun (handle, _) => result.2.contents handle) =
      .ok (xs.map (fun x => some (((ys.zipIdx 1).find? (fun p => JuliaLean.C.jlEqFloat x p.1)).map
        (fun p => JInt.wrap .i64 (p.2 : Int)))))

theorem indexinMembershipAgreement_refuted : ¬ IndexinMembershipAgreement := by
  intro h
  have bad := h [JuliaLean.Promotion.Fl.zero true] [JuliaLean.Promotion.Fl.zero false] ⟨[], []⟩
  change (Except.ok [some none] : Except Error (List (Option (Option I)))) =
    .ok [some (some one)] at bad
  cases bad

/-- A deletion exception must preserve every original vector slot. The iterator
and each copy are the source-mirrored array methods, over concrete memory. -/
def DeleteatErrorUnchanged : Prop :=
  ∀ (α : Type) (xs : List α) (indices : List I) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some → xs.length < 2 ^ 62 →
    let operation := deleteatIterator (m := MutationM α) mutableLength
      (listIterator indices) Subtype.val (· + one)
      mutableBounds
      (pushDeleted mutableAssigned mutableGet
        (fun _ value => pure (pushNowhere value))
        (fun _ delta => pure (growendNowhere delta)))
      (copyItem mutableAssigned mutableGet mutableSet mutableUnset)
      (· - ·) (deleteend mutableStorage pure) 0 ()
    let result := operation.run initial
    (∃ e, result.1 = .error e) → result.2.contents = xs.map some

theorem deleteatErrorUnchanged_refuted : ¬ DeleteatErrorUnchanged := by
  intro h
  have bad := h Int [10, 20, 30, 40]
    [JInt.wrap .i64 1, JInt.wrap .i64 3, JInt.wrap .i64 5]
    (MutableMemory.initial (([10, 20, 30, 40] : List Int).map some))
    (by decide) rfl (by decide)
  simp only [deleteatIterator] at bad
  dsimp [listIterator] at bad
  dsimp [mutableLength, mutableVector, MutableMemory.initial,
    pushDeleted, mutableAssigned, memoryRead, copyItem, mutableGet, mutableSet,
    memoryWrite, zero, one, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits] at bad
  simp (config := { singlePass := true }) only [deleteatIterator.loop.eq_1] at bad
  dsimp [listIterator, mutableLength, mutableVector, MutableMemory.initial,
    pushDeleted, mutableAssigned, memoryRead, copyItem, mutableGet, mutableSet,
    memoryWrite, zero, one, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits] at bad
  simp (config := { singlePass := true }) only [deleteatIterator.loop.eq_1] at bad
  have hb := bad ⟨.bounds, by rfl⟩
  revert hb
  decide

/-- Appending the same source more than once uses the values present before the call. -/
def AppendManySnapshot : Prop :=
  ∀ (α : Type) (xs : List α) (sources : List (Option (List α))) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some →
    (∀ p ∈ sources.zipIdx, match p.1 with
      | none => True
      | some values => initial.validVector (p.2 + 1) ∧
          initial.contents (p.2 + 1) = values.map some) →
    xs.length < 2 ^ 62 →
    let handles := sources.zipIdx |>.map fun (source, i) => if source.isNone then 0 else i + 1
    let appendOne := fun (a source : Nat) => do
      let _ ← appendVector (m := MutationM α) (fun _ => false) pure mutableLength pure
        (growend mutableStorage pure (growendInternal mutableStorage)) mutableLength
        (fun _ => pure one) mutableCopyto a source
      pure ()
    let prependOne := fun (a source : Nat) => do
      let _ ← prependVector (m := MutationM α) (fun _ => false) pure
        (fun source a => source == a) (fun _ source => pure source)
        mutableLength (growbeg mutableStorage pure (growbegInternal mutableStorage))
        mutableLength mutableCopyto a source
      pure ()
    let afterAppend := (appendMany appendOne 0 handles).run initial
    let afterPrepend := (prependMany prependOne 0 handles).run initial
    (afterAppend.1 = .ok 0 ∧ afterAppend.2.contents =
      (xs ++ sources.flatMap (·.getD xs)).map some) ∧
    (afterPrepend.1 = .ok 0 ∧ afterPrepend.2.contents =
      (sources.flatMap (·.getD xs) ++ xs).map some)

theorem appendManySnapshot_refuted : ¬ AppendManySnapshot := by
  intro h
  have bad := h Int [1, 2, 3] [none, none]
    (MutableMemory.initialMany [([1, 2, 3] : List Int).map some,
      ([1, 2, 3] : List Int).map some, ([1, 2, 3] : List Int).map some])
    (by decide) rfl (by simp) (by decide)
  have hb := bad.1.2
  change ([some 1, some 2, some 3, some 1, some 2, some 3,
    some 1, some 2, some 3, some 1, some 2, some 3] : List (Option Int)) =
      [some 1, some 2, some 3, some 1, some 2, some 3, some 1, some 2, some 3] at hb
  cases hb

/-- Replacement conversion failure must not expose new unassigned slots. -/
def SpliceErrorAssigned : Prop :=
  ∀ (α β : Type) (convert : β → Except Error α) (xs : List α) (lo hi : I) (ins : List β)
    (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some →
    xs.length < 2 ^ 62 → lo.val ≤ hi.val + 1 →
    let remove := deleteatWindow (m := MutationM α) pure mutableLength Subtype.val
      (· + ·) (· - ·) (fun a b => decide (a ≤ b)) (· - ·)
      mutableCopy mutableCopy (deletebeg mutableStorage pure) (deleteend mutableStorage pure)
    let operation := spliceRange (m := MutationM α)
      (getindexUnitRange Subtype.val
        (fun a (r : I × I) => do
          let n ← mutableLength a
          if !(r.1 > r.2) && !(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds)
        (fun r => r.2 - r.1 + one) (fun r => r.2 - r.1 + one)
        (fun a n => similar419 (mutableAllocate a) a n)
        (fun _ => pure one) Prod.fst mutableCopyto)
      (fun values => JInt.wrap .i64 values.length)
      (fun a r => do
        let _ ← deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
          (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
          (fun r => r.2 - r.1 + one) remove a r
        pure ())
      mutableLength Prod.fst Prod.snd (fun r => r.2 - r.1 + one) Subtype.val
      (· - ·) (· - ·) (fun a b => decide (a < b)) (· - ·) (· - ·)
      (· - ·) (· + one) (· + ·) (· - one) remove
      (growat mutableStorage pure pure
        (growbeg mutableStorage pure (growbegInternal mutableStorage))
        (growend mutableStorage pure (growendInternal mutableStorage)))
      (fun a value i => do
        let x ← liftM (convert value)
        mutableSet a x i)
      0 (lo, hi) ins
    let result := operation.run initial
    (∃ e, result.1 = .error e) → ∀ x ∈ result.2.contents, x.isSome = true

theorem spliceErrorAssigned_refuted : ¬ SpliceErrorAssigned := by
  intro h
  have bad := h String (Sum String Int)
    (fun x => match x with | .inl s => .ok s | .inr _ => .error (.method "convert"))
    ["a", "b", "c"] (JInt.wrap .i64 2) (JInt.wrap .i64 1)
    [.inl "x", .inr 1] (MutableMemory.initial ((["a", "b", "c"] : List String).map some))
    (by decide) rfl (by decide) (by decide)
  have hb := bad ⟨.method "convert", by rfl⟩
  revert hb
  decide

/-- Multidimensional search returns the first matching Cartesian key, including
the empty-array case, without reading an out-of-bounds element. -/
def FindfirstCartesian : Prop :=
  ∀ (dims : List Nat) (values : List I → Bool),
    (∀ n ∈ dims, n < 2 ^ 20) →
    findfirstArray (m := Except Error)
      (fun shape => .ok (shape.map (fun _ => one)))
      (fun test shape start =>
        findnext
          (fun shape => shape.map (fun _ => one))
          (fun shape => shape.map (fun (n : Nat) => JInt.wrap .i64 (n : Int)))
          (fun _ i => .ok i) cartesianGreater
          (fun shape key => if key ∈ cartesianKeys shape then .ok (values key) else .error .bounds)
          test (cartesianRank shape) (cartesianNext shape) shape start)
      (fun value => .ok value) dims =
        .ok ((cartesianKeys dims).find? values)

theorem findfirstCartesian_refuted : ¬ FindfirstCartesian := by
  intro h
  have bad := h [0, 3] (fun _ => false) (by simp)
  simp only [findfirstArray, findnext] at bad
  change findnext.loop _ _ _ _ _ _ _ = _ at bad
  delta findnext.loop at bad
  rw [WellFounded.Nat.fix_eq] at bad
  contradiction

/-- Range/vector intersection preserves the first argument's encounter order,
as does intersection with the corresponding collected range. -/
def IntersectRangeVectorOrder : Prop :=
  ∀ (range vector : List Int),
    let specialised := fun vector range =>
      intersectVectorRange (m := StateT (List Int) (MutationM Int)) (fun _ _ => ())
        (fun range value => decide (value ∈ range)) (fun test values => values.filter test)
        (fun _ common => do set common.eraseDups; pure ())
        (shrinkFilter (fun value _ => do return value ∈ (← get))
          (fun _ value => modify (fun values => values.erase value)))
        (fun _ test values => vectorfilter
          (typedLiteral (fun n => liftM (mutableAllocate (α := Int) 0 n))
            (fun a x i => liftM (mutableTypedSet (α := Int) a x i)) true)
          test values) vector range
    let forward := ((specialised vector range).run []).run ⟨[], []⟩
    let backward := ((intersectRangeVector specialised range vector).run []).run ⟨[], []⟩
    forward.1.map (fun (handle, _) => forward.2.contents handle) =
      .ok ((vector.filter (fun x => decide (x ∈ range))).eraseDups.map some) ∧
    backward.1.map (fun (handle, _) => backward.2.contents handle) =
      .ok ((range.filter (fun x => decide (x ∈ vector))).eraseDups.map some)

theorem intersectRangeVectorOrder_refuted : ¬ IntersectRangeVectorOrder := by
  intro h
  have bad := (h [1, 2, 3] [3, 2, 1]).2
  change (Except.ok [some 3, some 2, some 1] : Except Error (List (Option Int))) =
    .ok [some 1, some 2, some 3] at bad
  cases bad

/-- The complete old range-deletion contract, including overflowing range
lengths, requires BoundsError for a range outside the vector and no partial write. -/
def DeleteatRangeSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (xs : List α) (lo hi : JInt t) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some →
    xs.length < 2 ^ 62 → lo.val ≤ hi.val + 1 →
    IntTy.i64.min ≤ lo.val → hi.val ≤ IntTy.i64.max →
    let countType := if t.bits < 64 then IntTy.i64 else t
    let arithmeticType := IntTy.promote .i64 countType
    let remove := deleteatWindow (m := MutationM α)
      (fun i : JInt t => liftM (indexConvert i)) mutableLength
      (fun d : JInt countType => d.val)
      (fun a d => JInt.wrap arithmeticType (a.val + d.val))
      (fun a d => JInt.wrap arithmeticType (a.val - d.val))
      (fun a b => decide (a.val ≤ b.val))
      (fun a i => JInt.wrap arithmeticType (a.val - i.val))
      (fun a d b s n => do mutableCopy a (← liftM (indexConvert d)) b s n)
      (fun a d b s n => do mutableCopy a d b (← liftM (indexConvert s)) (← liftM (indexConvert n)))
      (deletebeg mutableStorage (fun d => liftM (indexConvert d)))
      (deleteend mutableStorage (fun d => liftM (indexConvert d)))
    let operation := deleteatRange (m := MutationM α)
      (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
      (fun _ _ => pure ()) (fun r => decide (r.1.val > r.2.val))
      (fun r => JInt.wrap countType (if r.1.val > r.2.val then 0 else r.2.val - r.1.val + 1))
      remove 0 (lo, hi)
    let result := operation.run initial
    (result.1, result.2.contents) =
      if lo.val > hi.val then (.ok 0, xs.map some)
      else if 1 ≤ lo.val ∧ hi.val ≤ (xs.length : Int) then
        (.ok 0, (xs.take (lo.val - 1).toNat ++ xs.drop hi.val.toNat).map some)
      else (.error .bounds, xs.map some)

theorem deleteatRangeSpec_refuted : ¬ DeleteatRangeSpec := by
  intro h
  have bad := h Int .i64 [1, 2, 3] (JInt.wrap .i64 (-1)) (JInt.typemax .i64)
    (MutableMemory.initial (([1, 2, 3] : List Int).map some))
    (by decide)
    rfl (by decide) (by decide) (by decide) (by decide)
  have errors := congrArg (fun result => result.1) bad
  change (Except.error (.argument "_deleteat! requires delta >= 0") : Except Error Nat) =
    Except.error .bounds at errors
  cases errors

/-- The real runtime barrier returns `nothing`; a nonempty iterator reaches
Julia's non-boolean condition error before another iteration step. -/
theorem iterator_upper_runtime_nonboolean (α : Type) (value : α) (tail : List α) :
    iteratorUpperBound (m := Except Error) (listIterator (value :: tail)) (.ok ())
      (fun _ => .error (.typeError "if")) = .error (.typeError "if") := by
  rw [iteratorUpperBound]
  change iteratorUpperBound.loop (m := Except Error) (listIterator (value :: tail)) (Except.ok ())
    (fun _ => Except.error (.typeError "if")) value tail = _
  rw [iteratorUpperBound.loop.eq_1]
  rfl

theorem empty_memory_get_bounds (α : Type) (i : I) :
    (mutableGet (α := α) 0 i).run
      ⟨[[]], [⟨(0, one), zero⟩]⟩ =
        (.error .bounds, ⟨[[]], [⟨(0, one), zero⟩]⟩) := by
  have invalid : ¬ (1 ≤ i.val ∧ i ≤ zero) := by
    change ¬ (1 ≤ i.val ∧ i.val ≤ 0)
    omega
  change ((if !(decide (1 ≤ i.val ∧ i ≤ zero)) then
      (fun s : MutableMemory α => ((Except.error .bounds : Except Error α), s))
    else _) ⟨[[]], [⟨(0, one), zero⟩]⟩) = _
  simp only [invalid, decide_false, Bool.not_false, ↓reduceIte]

/-- Empty concatenation produces a zero-length Vector{Any}; no integer index
can read an element. The default DimensionMismatch has the empty message. -/
def EmptyConcatSpec : Prop :=
  dimensionMismatch.message = "" ∧
  ∀ (α : Type) (i : I),
    let allocate := fun n => do
      let handle ← mutableAllocate (α := α) 0 n
      pure (StoredType.any, handle)
    (∃ handle memory,
      (vcatEmpty allocate).run ⟨[], []⟩ = (.ok (.any, handle), memory) ∧
      (mutableLength (α := α) handle).run memory = (.ok zero, memory) ∧
      memory.contents handle = [] ∧
      (mutableGet (α := α) handle i).run memory = (.error .bounds, memory)) ∧
    (∃ handle memory,
      (hcatEmpty allocate).run ⟨[], []⟩ = (.ok (.any, handle), memory) ∧
      (mutableLength (α := α) handle).run memory = (.ok zero, memory) ∧
      memory.contents handle = [] ∧
      (mutableGet (α := α) handle i).run memory = (.error .bounds, memory))

theorem emptyConcatSpec : EmptyConcatSpec := by
  refine ⟨rfl, ?_⟩
  intro α i
  constructor
  · exact ⟨0, ⟨[[]], [⟨(0, one), zero⟩]⟩, rfl, rfl, rfl, empty_memory_get_bounds α i⟩
  · exact ⟨0, ⟨[[]], [⟨(0, one), zero⟩]⟩, rfl, rfl, rfl, empty_memory_get_bounds α i⟩

/-- The number of reads and writes in an expression is unchanged by safe indexing. -/
def indexOperations : Expr Atom → Nat
  | .atom _ => 0
  | .node _ args => (args.map indexOperations).sum
  | .ref xs args => indexOperations xs + 1 + (args.map indexOperations).sum
  | .assign lhs rhs => indexOperations lhs + indexOperations rhs
  | .safeGet xs args => indexOperations xs + 1 + (args.map indexOperations).sum
  | .safeSet xs rhs args =>
      indexOperations xs + 1 + indexOperations rhs + (args.map indexOperations).sum
  | .escape body => indexOperations body
termination_by e => sizeOf e

def SafeindexSpec : Prop := ∀ (Atom : Type) (e : Expr Atom),
  indexOperations (safeindex e) = indexOperations e ∧
  indexOperations (safeindexMacro safeindex e) = indexOperations e

theorem safeindex_operations (e : Expr Atom) :
    indexOperations (safeindex e) = indexOperations e := by
  induction e using safeindex.induct with
  | case1 => simp [safeindex, indexOperations]
  | case2 xs args rhs hr ha =>
    have hm : (args.map (fun x => indexOperations (safeindex x))).sum =
        (args.map indexOperations).sum := by
      congr 1
      exact List.map_congr_left ha
    simp only [safeindex, indexOperations, List.map_map, Function.comp_def]
    rw [hr, hm]
    omega
  | case3 => simp [safeindex, indexOperations]
  | case4 lhs rhs hl hr =>
    cases lhs <;> simp_all [safeindex, indexOperations]
  | case5 h args ha =>
    simp only [safeindex, indexOperations, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    exact ha x hx
  | case6 xs args hx ha =>
    simp only [safeindex, indexOperations, List.map_map]
    rw [hx]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro x h
    exact ha x h
  | case7 xs x args hx hv ha =>
    simp only [safeindex, indexOperations, List.map_map]
    rw [hx, hv]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro a h
    exact ha a h
  | case8 x hx => simpa only [safeindex, indexOperations] using hx

theorem safeindexSpec : SafeindexSpec := by
  intro Atom e
  exact ⟨safeindex_operations e, by
    simpa only [safeindexMacro, indexOperations] using safeindex_operations e⟩

/-- Safe-call constructors are introduced by the rewrite, not by the input AST. -/
def ordinaryExpression : Expr Atom → Prop
  | .atom _ => True
  | .node _ args => ∀ x ∈ args, ordinaryExpression x
  | .ref xs args => ordinaryExpression xs ∧ ∀ x ∈ args, ordinaryExpression x
  | .assign lhs rhs => ordinaryExpression lhs ∧ ordinaryExpression rhs
  | .escape x => ordinaryExpression x
  | .safeGet _ _ | .safeSet _ _ _ => False
termination_by e => sizeOf e

def restoreIndexing : Expr Atom → Expr Atom
  | .atom x => .atom x
  | .node h args => .node h (args.map restoreIndexing)
  | .ref xs args => .ref (restoreIndexing xs) (args.map restoreIndexing)
  | .assign lhs rhs => .assign (restoreIndexing lhs) (restoreIndexing rhs)
  | .safeGet xs args => .ref (restoreIndexing xs) (args.map restoreIndexing)
  | .safeSet xs x args =>
      .assign (.ref (restoreIndexing xs) (args.map restoreIndexing)) (restoreIndexing x)
  | .escape x => .escape (restoreIndexing x)
termination_by e => sizeOf e

theorem restoreIndexing_ordinary (e : Expr Atom) (he : ordinaryExpression e) :
    restoreIndexing e = e := by
  cases e with
  | atom x => simp [restoreIndexing]
  | node h args =>
    simp only [restoreIndexing]
    simp only [ordinaryExpression] at he
    have hm : args.map restoreIndexing = args := by
      calc
        args.map restoreIndexing = args.map id :=
          List.map_congr_left (fun x hx => restoreIndexing_ordinary x (he x hx))
        _ = args := List.map_id args
    rw [hm]
  | ref xs args =>
    simp only [ordinaryExpression] at he
    have hm : args.map restoreIndexing = args := by
      calc
        args.map restoreIndexing = args.map id :=
          List.map_congr_left (fun x hx => restoreIndexing_ordinary x (he.2 x hx))
        _ = args := List.map_id args
    simp only [restoreIndexing]
    rw [restoreIndexing_ordinary xs he.1, hm]
  | assign lhs rhs =>
    simp only [ordinaryExpression] at he
    simp only [restoreIndexing]
    rw [restoreIndexing_ordinary lhs he.1, restoreIndexing_ordinary rhs he.2]
  | escape x =>
    simp only [ordinaryExpression] at he
    simp only [restoreIndexing]
    rw [restoreIndexing_ordinary x he]
  | safeGet xs args => simp only [ordinaryExpression] at he
  | safeSet xs x args => simp only [ordinaryExpression] at he
termination_by sizeOf e

theorem safeindex_restore (e : Expr Atom) (he : ordinaryExpression e) :
    restoreIndexing (safeindex e) = e := by
  revert he
  induction e using safeindex.induct with
  | case1 => intro he; simp [safeindex, restoreIndexing]
  | case2 xs args rhs hr ha =>
    intro he
    simp only [ordinaryExpression] at he
    have hm : (args.map safeindex).map restoreIndexing = args := by
      rw [List.map_map]
      calc
        args.map (restoreIndexing ∘ safeindex) = args.map id :=
          List.map_congr_left (fun x hx => ha x hx (he.1.2 x hx))
        _ = args := List.map_id args
    simp only [safeindex, restoreIndexing]
    rw [restoreIndexing_ordinary xs he.1.1, hr he.2, hm]
  | case3 xs args =>
    intro he
    simpa only [safeindex, restoreIndexing] using restoreIndexing_ordinary (.ref xs args) he
  | case4 lhs rhs hl hr =>
    intro he
    cases lhs <;> simp_all [ordinaryExpression, safeindex, restoreIndexing]
  | case5 h args ha =>
    intro he
    simp only [ordinaryExpression] at he
    have hm : (args.map safeindex).map restoreIndexing = args := by
      rw [List.map_map]
      calc
        args.map (restoreIndexing ∘ safeindex) = args.map id :=
          List.map_congr_left (fun x hx => ha x hx (he x hx))
        _ = args := List.map_id args
    simp only [safeindex, restoreIndexing]
    rw [hm]
  | case6 => intro he; simp only [ordinaryExpression] at he
  | case7 => intro he; simp only [ordinaryExpression] at he
  | case8 x hx =>
    intro he
    simp only [ordinaryExpression] at he
    simp only [safeindex, restoreIndexing]
    rw [hx he]

def SafeindexComplete : Prop := SafeindexSpec ∧ ∀ (Atom : Type) (e : Expr Atom),
  ordinaryExpression e →
    restoreIndexing (safeindex e) = e ∧
    restoreIndexing (safeindexMacro safeindex e) = .escape e

theorem safeindexComplete : SafeindexComplete := by
  refine ⟨safeindexSpec, ?_⟩
  intro Atom e he
  exact ⟨safeindex_restore e he, by
    simp only [safeindexMacro, restoreIndexing]
    rw [safeindex_restore e he]⟩

/-- A single fresh allocation's reference slots. These primitives belong to
`essentials.jl` and `memory.jl`; stores in literals use array.jl's safe setter. -/
abbrev LiteralM (α : Type) := StateM (List (Option α))

def literalAllocate (n : I) : LiteralM α Unit :=
  fun _ => ((), List.replicate n.val.toNat none)

def literalRef (_a : A) (i : I) (_checked : Bool) : LiteralM α I := fun slots => (i, slots)

def literalStore (i : I) (x : α) (_checked : Bool) : LiteralM α Unit :=
  fun slots => ((), slots.set (i.val - 1).toNat (some x))

theorem literal_counter (k : Nat) (hk : k + 1 < 2 ^ 63) :
    (JInt.wrap .i64 (k + 1)).val = k + 1 := by
  change wrapInt .i64 ((k : Int) + 1) = (k : Int) + 1
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  omega

theorem literal_write_tail (tail done : List α) (handle : A)
    (hn : done.length + tail.length < 2 ^ 63) :
    ((tail.foldlM (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (JInt.wrap .i64 (done.length + 1), handle)).run
        (done.map some ++ List.replicate tail.length none)).2 =
      (done ++ tail).map some := by
  induction tail generalizing done with
  | nil =>
    simp only [List.foldlM_nil, List.length_nil, List.replicate_zero, List.append_nil]
    rfl
  | cons x tail ih =>
    have hi := literal_counter done.length (by simp only [List.length_cons] at hn; omega)
    have hnext : JInt.wrap .i64 (done.length + 1) + one =
        JInt.wrap .i64 ((done ++ [x]).length + 1) := by
      apply Subtype.ext
      change wrapInt .i64 ((JInt.wrap .i64 (done.length + 1)).val + one.val) = _
      rw [hi]
      rw [show one.val = 1 from rfl]
      change wrapInt .i64 ((done.length : Int) + 1 + 1) =
        wrapInt .i64 (((done ++ [x]).length : Int) + 1)
      apply congrArg (wrapInt .i64)
      simp only [List.length_append, List.length_singleton, Int.natCast_add, Int.natCast_one]
    have hslot :
        (done.map some ++ List.replicate (x :: tail).length none).set
          ((JInt.wrap .i64 (done.length + 1)).val - 1).toNat (some x) =
          (done ++ [x]).map some ++ List.replicate tail.length none := by
      rw [hi]
      simp [List.length_map, List.replicate_succ, List.map_append, List.append_assoc]
    have hind := ih (done ++ [x]) (by
      simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hn
      omega)
    rw [List.foldlM_cons]
    change ((tail.foldlM (m := LiteralM α) (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (JInt.wrap .i64 (done.length + 1) + one, handle)).run
      ((done.map some ++ List.replicate (x :: tail).length none).set
        ((JInt.wrap .i64 (done.length + 1)).val - 1).toNat (some x))).2 = _
    rw [hslot, hnext]
    simpa only [List.append_assoc, List.singleton_append] using hind

def LiteralContents : Prop := ∀ (α : Type) (xs : List α) (old : List (Option α)),
  xs.length < 2 ^ 63 →
  (vectTyped literalAllocate (safeSetindex1057 literalRef literalStore) xs).run old =
    ((), xs.map some) ∧
  (typedLiteral literalAllocate (safeSetindex1057 literalRef literalStore) true xs).run old =
    ((), xs.map some) ∧
  (typedLiteral literalAllocate (safeSetindex1057 literalRef literalStore) false xs).run old =
    ((), xs.map some) ∧
  (anyLiteral literalAllocate (safeSetindex1055 literalRef literalStore) xs).run old =
    ((), xs.map some)

theorem state_unit_finish (action : StateM σ (β × Unit)) (state : σ) :
    ((do let (_, a) ← action; pure a) : StateM σ Unit).run state =
      ((), (action.run state).2) := by
  rfl

theorem vectTyped_state_run (allocate : I → StateM σ A)
    (store : A → α → I → StateM σ A) (xs : List α) (state : σ) :
    (vectTyped allocate store xs).run state =
      (writeValues store ((allocate (JInt.wrap .i64 xs.length)).run state).1 xs).run
        ((allocate (JInt.wrap .i64 xs.length)).run state).2 := by
  rfl

theorem typedLiteral_eq_vect [Monad m] (allocate : I → m A)
    (store : A → α → I → m A) (homogeneous : Bool) (xs : List α) :
    typedLiteral allocate store homogeneous xs = vectTyped allocate store xs := by
  cases homogeneous <;> rfl

theorem anyLiteral_eq_vect [Monad m] (allocate : I → m A)
    (store : A → α → I → m A) (xs : List α) :
    anyLiteral allocate store xs = vectTyped allocate store xs := by
  rfl

theorem literalContents : LiteralContents := by
  intro α xs old hn
  have hlen : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
    change wrapInt .i64 (xs.length : Int) = xs.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have h := literal_write_tail xs [] () (by simpa using hn)
  simp only [List.length_nil, Int.natCast_zero, Int.zero_add, List.map_nil,
    List.nil_append] at h
  have hw : (writeValues (safeSetindex1057 literalRef literalStore) () xs).run
      (List.replicate xs.length none) = ((), xs.map some) := by
    rw [writeValues, state_unit_finish]
    exact congrArg (fun s => ((), s)) h
  have ha : (literalAllocate (α := α) (JInt.wrap .i64 xs.length)).run old =
      ((), List.replicate xs.length none) := by
    change ((), List.replicate (JInt.wrap .i64 xs.length).val.toNat none) = _
    rw [hlen, Int.toNat_natCast]
  have hv : (vectTyped literalAllocate (safeSetindex1057 literalRef literalStore) xs).run old =
      ((), xs.map some) := by
    rw [vectTyped_state_run, ha]
    exact hw
  refine ⟨hv, ?_, ?_, ?_⟩
  · rw [typedLiteral_eq_vect]
    exact hv
  · rw [typedLiteral_eq_vect]
    exact hv
  · rw [anyLiteral_eq_vect]
    exact hv

/-- Fixed-length, one-based memory primitives from essentials.jl and memory.jl. -/
abbrev SlotM (α : Type) := ExceptT Error (StateM (I → Option α))

def updateSlot (slots : I → Option α) (i : I) (value : Option α) : I → Option α :=
  fun j => if j = i then value else slots j

def slotBounds (n : Nat) (_a : Unit) (i : I) : SlotM α Unit :=
  fun slots => (if 1 ≤ i.val ∧ i.val ≤ (n : Int) then .ok () else .error .bounds, slots)

def slotRef (_a : Unit) (i : I) : SlotM α I := fun slots => (.ok i, slots)

def slotRefNew (_a : Unit) (i : I) (_checked : Bool) : SlotM α I :=
  fun slots => (.ok i, slots)

def slotUnset (i : I) : SlotM α Unit :=
  fun slots => (.ok (), updateSlot slots i none)

def slotStore (i : I) (x : α) (_checked : Bool) : SlotM α Unit :=
  fun slots => (.ok (), updateSlot slots i (some x))

def slotRead (i : I) : SlotM α α :=
  fun slots => (match slots i with | some x => .ok x | none => .error .undefinedReference, slots)

def slotLift (value : Except Error α) : SlotM β α := fun slots => (value, slots)

def LinearAccessSpec : Prop := ∀ (α β : Type) (n : Nat) (slots : I → Option α)
    (i : I) (x : α) (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (v : β),
  let inb := 1 ≤ i.val ∧ i.val ≤ (n : Int)
  let converted := if already v then .ok (asTyped v) else convert v
  (unsetindexInt (slotBounds n) slotRef slotUnset () i).run slots =
    (if inb then (.ok (), updateSlot slots i none) else (.error .bounds, slots)) ∧
  (setindexTyped (slotBounds n) slotRefNew slotStore () x i).run slots =
    (if inb then (.ok (), updateSlot slots i (some x)) else (.error .bounds, slots)) ∧
  (inb → (do
    let _ ← setindexTyped (slotBounds n) slotRefNew slotStore () x i
    slotRead i : SlotM α α).run slots =
      (.ok x, updateSlot slots i (some x))) ∧
  (∀ e, converted = .error e →
    (setindexScalar already asTyped (fun v => slotLift (convert v))
      (setindexTyped (slotBounds n) slotRefNew slotStore) () v i).run slots =
      (.error e, slots)) ∧
  (∀ y, converted = .ok y →
    (setindexScalar already asTyped (fun v => slotLift (convert v))
      (setindexTyped (slotBounds n) slotRefNew slotStore) () v i).run slots =
      (if inb then (.ok (), updateSlot slots i (some y)) else (.error .bounds, slots))) ∧
  (inb → ∀ j, j ≠ i →
    (updateSlot slots i (some x)) j = slots j ∧
    (updateSlot slots i none) j = slots j)

theorem linearAccessSpec : LinearAccessSpec := by
  intro α β n slots i x already asTyped convert v inb converted
  cases ha : already v <;> cases hc : convert v <;>
    by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int) <;>
    simp [inb, converted, ha, hc, hb, unsetindexInt, setindexTyped, setindexScalar, slotBounds,
      slotRef, slotRefNew, slotUnset, slotStore, slotRead, slotLift, updateSlot,
      ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      StateT.bind, StateT.pure, Bind.bind, Pure.pure]
  all_goals
    intro a ha hne
    constructor <;> intro he <;> exact (hne he).elim

def AssignmentSpec : Prop := ∀ (α : Type) (slots : I → Option α) (n : Nat) (i : I),
  (isassignedVector (m := Id) (fun (_ : Unit) j => decide (1 ≤ j.val ∧ j.val ≤ (n : Int)))
    (fun _ j _ => j) (fun j => (slots j).isSome) () i = true ↔
      1 ≤ i.val ∧ i.val ≤ (n : Int) ∧ ∃ x, slots i = some x) ∧
  ∀ (D : Type) (dims : D) (bounds : List I → Bool) (linear : D → List I → I)
      (indices : List I),
    (isassignedArray (m := Id) (fun (_ : Unit) js => bounds js) (fun _ => dims)
      linear (fun _ j _ => j) (fun j => (slots j).isSome) () indices = true ↔
        bounds indices = true ∧ ∃ x, slots (linear dims indices) = some x)

theorem assignmentSpec : AssignmentSpec := by
  intro α slots n i
  constructor
  · by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int)
    · cases hs : slots i <;> simp [isassignedVector, hb, hs, Bind.bind]
    · have hb' : ¬ (1 ≤ i.val ∧ i.val ≤ (n : Int) ∧ ∃ x, slots i = some x) :=
        fun h => hb ⟨h.1, h.2.1⟩
      simp only [isassignedVector, show decide (1 ≤ i.val ∧ i.val ≤ (n : Int)) = false
        from decide_eq_false hb, Bind.bind, Pure.pure, Bool.not_false, ite_true]
      exact ⟨fun h => Bool.noConfusion h, fun h => (hb' h).elim⟩
  · intro D dims bounds linear indices
    cases hb : bounds indices <;> cases hs : slots (linear dims indices) <;>
      simp [isassignedArray, hb, hs, Bind.bind, Pure.pure]

def EmptyLiteralSpec : Prop := ∀ (α : Type) (old : List (Option α)),
  (vectEmpty (literalAllocate (α := α))).run old = ((), []) ∧
  (anyLiteralEmpty (literalAllocate (α := α))).run old = ((), [])

theorem emptyLiteralSpec : EmptyLiteralSpec := by
  intro α old
  exact ⟨rfl, rfl⟩

theorem mapM_ok_of_mem (f : α → Except Error β) (g : α → β) (xs : List α)
    (h : ∀ x ∈ xs, f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem dimension_range_suffix (size : List I → I → Except Error I)
    (hsize : ∀ dims i, size dims i =
      if 1 ≤ i.val then .ok (dims[(i.val - 1).toNat]?.getD one) else .error .bounds)
    (dims : List I) (hd : dims.length < 2 ^ 63) (i : I)
    (hi : 1 ≤ i.val) (he : i.val ≤ (dims.length : Int)) :
    (intRange i (JInt.wrap .i64 dims.length)).mapM (size dims) =
      .ok (dims.drop (i.val - 1).toNat) := by
  have hdim : (JInt.wrap .i64 (dims.length : Int)).val = dims.length := by
    change wrapInt .i64 (dims.length : Int) = dims.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  let offset := (i.val - 1).toNat
  let count := dims.length - offset
  have hcount : ((dims.length : Int) - i.val + 1).toNat = count := by
    dsimp [count, offset]
    omega
  have hj : ∀ k, k < count →
      (JInt.wrap .i64 (i.val + (k : Int))).val = i.val + (k : Int) := by
    intro k hk
    change wrapInt .i64 (i.val + (k : Int)) = _
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    dsimp [count, offset] at hk
    omega
  unfold intRange
  rw [hdim, hcount, List.mapM_map]
  have hs : ∀ k ∈ List.range count,
      size dims (JInt.wrap .i64 (i.val + (k : Int))) =
        .ok (dims[offset + k]?.getD one) := by
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [hsize, hj k hk', ite_eq_left (by omega)]
    have hidx : (i.val + (k : Int) - 1).toNat = offset + k := by
      dsimp [offset]
      omega
    rw [hidx]
  simp only [Function.comp_def]
  rw [mapM_ok_of_mem _ _ _ hs]
  apply congrArg Except.ok
  apply List.ext_getElem
  · simp [count, offset]
  · intro k hk hk'
    have hlt : offset + k < dims.length := by
      simp only [List.length_map, List.length_range] at hk
      dsimp [count] at hk
      omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop,
      List.getElem?_eq_getElem hlt, Option.getD_some]
    rfl

def DimensionSuffixSpec : Prop :=
  ∀ (Z : Type) (value : Z → Int) (toInt : Z → Except Error I)
    (size : List I → I → Except Error I),
    (∀ n, toInt n = (JInt.convert .i64 (value n)).mapError (fun _ => Error.inexact)) →
    (∀ dims i, size dims i =
      if 1 ≤ i.val then .ok (dims[(i.val - 1).toNat]?.getD one) else .error .bounds) →
    ∀ (dims : List I) (n : Z), dims.length < 2 ^ 63 →
      (1 ≤ value n →
        asizeFrom value toInt (fun dims => JInt.wrap .i64 dims.length) size dims n =
          .ok (dims.drop (value n - 1).toNat)) ∧
      (IntTy.i64.min ≤ value n → value n ≤ 0 →
        asizeFrom value toInt (fun dims => JInt.wrap .i64 dims.length) size dims n =
          .error .bounds) ∧
      (value n < IntTy.i64.min →
        asizeFrom value toInt (fun dims => JInt.wrap .i64 dims.length) size dims n =
          .error .inexact)

theorem dimensionSuffixSpec : DimensionSuffixSpec := by
  intro Z value toInt size hconvert hsize dims n hd
  have hdim : (JInt.wrap .i64 (dims.length : Int)).val = dims.length := by
    change wrapInt .i64 (dims.length : Int) = dims.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hvalid (hb : IntTy.i64.min ≤ value n ∧ value n ≤ IntTy.i64.max) :
      toInt n = .ok ⟨value n, hb⟩ := by
    rw [hconvert]
    simp only [JInt.convert, dite_eq_left hb, Except.mapError]
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    by_cases hbig : value n > (dims.length : Int)
    · have hempty : dims.drop (value n - 1).toNat = [] :=
        List.drop_eq_nil_iff.mpr (by omega)
      rw [hempty]
      simp only [asizeFrom, hdim, hbig, ↓reduceIte]
      rfl
    · have hb : IntTy.i64.min ≤ value n ∧ value n ≤ IntTy.i64.max := by
        simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
        omega
      simp only [asizeFrom, hdim, hbig, ↓reduceIte, hvalid hb,
        Bind.bind, Except.bind]
      exact dimension_range_suffix size hsize dims hd ⟨value n, hb⟩ hn (by
        change value n ≤ (dims.length : Int)
        omega)
  · intro hmin hn
    have hb : IntTy.i64.min ≤ value n ∧ value n ≤ IntTy.i64.max := by
      constructor
      · exact hmin
      · have : (0 : Int) ≤ IntTy.i64.max := by decide
        omega
    have hbig : ¬ value n > (dims.length : Int) := by omega
    simp only [asizeFrom, hdim, hbig, ↓reduceIte, hvalid hb, Bind.bind, Except.bind]
    unfold intRange
    have hc : 0 < ((dims.length : Int) - value n + 1).toNat := by omega
    rw [hdim]
    change (List.mapM (size dims)
      ((List.range ((dims.length : Int) - value n + 1).toNat).map
        (fun k : Nat => JInt.wrap .i64 (value n + (k : Int))))) = _
    rw [show ((dims.length : Int) - value n + 1).toNat =
      (((dims.length : Int) - value n + 1).toNat - 1) + 1 by omega,
      List.range_succ_eq_map, List.map_cons, List.mapM_cons]
    have hv : (JInt.wrap .i64 (value n)).val = value n :=
      wrapInt_of_inRange .i64 (value n) hb
    simp only [Int.natCast_zero, Int.add_zero]
    rw [hsize, hv, ite_eq_right (by omega)]
    rfl
  · intro hn
    have hbig : ¬ value n > (dims.length : Int) := by
      have : IntTy.i64.min < 0 := by decide
      omega
    have hb : ¬ (IntTy.i64.min ≤ value n ∧ value n ≤ IntTy.i64.max) := by omega
    simp [asizeFrom, hdim, hbig, hconvert, JInt.convert, hb,
      Bind.bind, Except.bind, Except.mapError]

/-- The runtime layout interface supplies element sizes. The non-overflow
condition is the size invariant of an allocation that Julia can actually hold. -/
def ArrayStorageSizeSpec : Prop :=
  ∀ (aligned : StoredType → I)
    (_hbits : ∀ d : Layout, d.WF → d.isbits = true → d.size < 2 ^ 63 →
      (aligned (.dt d)).val = (d.size : Int))
    (_hboxed : ∀ t, allocatedinline storedInline t = false → aligned t = JInt.wrap .i64 8),
    (∀ (d : Layout) (n : I), d.WF → d.isbits = true → d.size < 2 ^ 63 → 0 ≤ n.val →
      n.val * (d.size : Int) ≤ IntTy.i64.max →
      (elsizeArray aligned (.dt d)).val = (d.size : Int) ∧
      (sizeofArray id (fun _ => elsizeArray aligned (.dt d)) n).val =
        n.val * (d.size : Int)) ∧
    (∀ t, allocatedinline storedInline t = false → (elsizeArray aligned t).val = 8) ∧
    elsizeBottom.val = 0 ∧
    ∀ (α : Type) (args : List α), elsizeBottomArgs (m := Except Error) args =
      .error (.method "elsize")

theorem arrayStorageSizeSpec : ArrayStorageSizeSpec := by
  intro aligned hbits hboxed
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro d n hw hb hd hn hmax
    have hs := hbits d hw hb hd
    refine ⟨hs, ?_⟩
    change wrapInt .i64 (n.val * (aligned (.dt d)).val) = _
    rw [hs]
    apply wrapInt_of_inRange
    constructor
    · have hm : 0 ≤ n.val * (d.size : Int) := Int.mul_nonneg hn (Int.natCast_nonneg _)
      have : IntTy.i64.min ≤ 0 := by decide
      omega
    · exact hmax
  · intro t ht
    change (aligned t).val = 8
    rw [hboxed t ht]
    rfl
  · intro α args
    rfl

def PointerStrideSpec : Prop :=
  ∀ (align : I → I → I)
    (_halign : ∀ d : Layout, d.WF → d.size < 2 ^ 63 → d.align < 2 ^ 63 →
      align (JInt.wrap .i64 d.size) (JInt.wrap .i64 d.align) = JInt.wrap .i64 d.size)
    (d : Layout) (_hw : d.WF) (_hsize : d.size < 2 ^ 63) (_hal : d.align < 2 ^ 63) (e : Error),
  let isAny : StoredType → Bool := fun t => match t with | .any => true | _ => false
  let isDT : StoredType → Bool := fun t => match t with | .dt _ | .abstractDT _ => true | _ => false
  let coreSize : StoredType → Except Error I := fun t =>
    match t with | .dt t => .ok (JInt.wrap .i64 t.size) | _ => .error e
  let alignment : StoredType → Except Error I := fun t =>
    match t with | .dt t => .ok (JInt.wrap .i64 t.align) | _ => .error e
  (elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8) coreSize alignment align (.dt d) =
    .ok (JInt.wrap .i64 d.size)) ∧
  (elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8) coreSize alignment align .any =
    .ok (JInt.wrap .i64 8)) ∧
  (elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8) coreSize alignment align .bottom =
    .error e) ∧
  (∀ members, elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8)
    coreSize alignment align (.union members) = .error e) ∧
  (∀ name, elsizePtr isAny isDT (.error e) (JInt.wrap .i64 8)
    coreSize alignment align (.abstractDT name) = .error e)

theorem pointerStrideSpec : PointerStrideSpec := by
  intro align halign d hw hsize hal e isAny isDT coreSize alignment
  simp [elsizePtr, isAny, isDT, coreSize, alignment, halign d hw hsize hal,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Lift a non-throwing state action into a state computation that can fail. -/
def liftLiteralState (action : StateM σ α) : StateT σ (Except Error) α :=
  fun state => .ok (action.run state)

theorem fold_converted_state (step : S → α → StateM σ S)
    (convert : β → Except Error α) (xs : List β) (start : S) (state : σ) :
    (xs.foldlM (fun s x => do
      let y ← StateT.lift (convert x)
      liftLiteralState (step s y)) start).run state =
      (do
        let ys ← xs.mapM convert
        pure ((ys.foldlM step start).run state) : Except Error (S × σ)) := by
  induction xs generalizing start state with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldlM_cons, List.mapM_cons]
    cases hc : convert x with
    | error e =>
      simp [StateT.lift, StateT.run, StateT.bind, Except.bind, Bind.bind]
    | ok y =>
      cases hs : step start y state with
      | mk next state' =>
        have h := ih next state'
        cases ht : xs.mapM convert <;>
          simpa [StateT.run_bind, StateT.lift, hc, ht, hs, liftLiteralState,
            StateT.run, StateT.bind, Except.bind, Except.pure, Bind.bind, Pure.pure,
            List.foldlM_cons] using h

theorem state_finish [Monad m] [LawfulMonad m] (action : StateT σ m (β × A)) (state : σ) :
    ((do let (_, a) ← action; pure a) : StateT σ m A).run state =
      (fun p => (p.1.2, p.2)) <$> (action.run state) := by
  simp only [bind_pure_comp, StateT.run_map]

def convertedLiteralSetter (convert : β → Except Error α) :
    A → β → I → StateT (List (Option α)) (Except Error) A :=
  safeSetindexConvert (fun x => StateT.lift (convert x))
    (safeSetindex1057 (fun a i b => liftLiteralState (literalRef a i b))
      (fun i x b => liftLiteralState (literalStore i x b)))

theorem converted_literal_step (convert : β → Except Error α) (p : I × A) (x : β) :
    (do
      let a ← convertedLiteralSetter convert p.2 x p.1
      pure (p.1 + one, a)) =
    (do
      let y ← StateT.lift (convert x)
      liftLiteralState (do
        let a ← safeSetindex1057 literalRef literalStore p.2 y p.1
        pure (p.1 + one, a))) := by
  funext state
  cases hc : convert x <;>
    simp [convertedLiteralSetter, safeSetindexConvert, safeSetindex1057,
      liftLiteralState, literalRef, literalStore, hc, StateT.run, StateT.bind,
      StateT.lift, StateT.pure, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem converted_length (convert : β → Except Error α) (xs : List β)
    (ys : List α) (h : xs.mapM convert = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst ys
    rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hc : convert x <;> cases ht : xs.mapM convert <;>
      simp [hc, ht, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    subst ys
    simp only [List.length_cons]
    rw [ih _ ht]

def literalAllocateAs (handle : A) (n : I) : LiteralM α A :=
  fun _ => (handle, List.replicate n.val.toNat none)

theorem literal_keeps_handle (xs : List α) (i : I) (handle : A) (old : List (Option α)) :
    ((xs.foldlM (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (i, handle)).run old).1.2 = handle := by
  induction xs generalizing i old with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldlM_cons]
    change ((xs.foldlM (m := LiteralM α) (s := I × A) (fun (i, a) x => do
      let a ← safeSetindex1057 literalRef literalStore a x i
      pure (i + one, a)) (i + one, handle)).run
      (old.set (i.val - 1).toNat (some x))).1.2 = handle
    exact ih (i + one) _

def ConvertedLiteralContents : Prop := ∀ (α β A : Type) (handle : A)
    (convert : β → Except Error α) (homogeneous : Bool) (xs : List β) (old : List (Option α)),
  xs.length < 2 ^ 63 →
  (typedLiteral (fun n => liftLiteralState (literalAllocateAs handle n))
    (convertedLiteralSetter convert) homogeneous xs).run old =
      (xs.mapM convert).map (fun ys => (handle, ys.map some))

theorem except_ok_bind (x : S) (f : S → Except Error A) :
    (Except.ok x >>= f) = f x := by rfl

theorem except_finish (value : Except Error S) (f : S → A) (g : A → B) :
    g <$> (do let x ← value; pure (f x)) = value.map (fun x => g (f x)) := by
  cases value <;> rfl

theorem vectTyped_fallible_run (handle : A) (store : A → β → I →
    StateT (List (Option α)) (Except Error) A) (xs : List β) (old : List (Option α)) :
    (vectTyped (fun n => liftLiteralState (literalAllocateAs handle n)) store xs).run old =
      (writeValues store handle xs).run
        (List.replicate (JInt.wrap .i64 xs.length).val.toNat none) := by
  have ha : (liftLiteralState (literalAllocateAs (α := α) handle
      (JInt.wrap .i64 xs.length))).run old =
        .ok (handle, List.replicate (JInt.wrap .i64 xs.length).val.toNat none) := by
    rfl
  rw [vectTyped, StateT.run_bind, ha, except_ok_bind]

theorem convertedLiteralContents : ConvertedLiteralContents := by
  intro α β A handle convert homogeneous xs old hn
  rw [typedLiteral_eq_vect]
  have hlen : (JInt.wrap .i64 (xs.length : Int)).val.toNat = xs.length := by
    have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
      change wrapInt .i64 (xs.length : Int) = xs.length
      apply wrapInt_of_inRange
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega
    rw [hv, Int.toNat_natCast]
  rw [vectTyped_fallible_run, hlen]
  rw [writeValues, state_finish]
  simp only [converted_literal_step]
  rw [fold_converted_state, except_finish]
  cases hc : xs.mapM convert with
  | error e => rfl
  | ok ys =>
    have hy : ys.length = xs.length := converted_length convert xs ys hc
    have hw := literal_write_tail ys [] handle (by simp only [List.length_nil, Nat.zero_add, hy]; exact hn)
    simp only [List.length_nil, Int.natCast_zero, Int.zero_add, List.map_nil, List.nil_append] at hw
    simp only [Except.map]
    apply congrArg Except.ok
    apply Prod.ext
    · exact literal_keeps_handle ys one handle _
    · simpa only [hy, one] using hw

def PromotedLiteralContents : Prop := ∀ (α β T : Type)
    (promote : List β → T) (convert : T → β → Except Error α)
    (homogeneous : Bool) (xs : List β) (old : List (Option α)),
  xs.length < 2 ^ 63 →
  (vectPromoted promote (fun t vals =>
    typedLiteral (fun n => liftLiteralState (literalAllocateAs t n))
      (convertedLiteralSetter (convert t)) homogeneous vals) xs).run old =
    (xs.mapM (convert (promote xs))).map (fun ys => (promote xs, ys.map some))

theorem promotedLiteralContents : PromotedLiteralContents := by
  intro α β T promote convert homogeneous xs old hn
  exact convertedLiteralContents α β T (promote xs) (convert (promote xs))
    homogeneous xs old hn

def StorageSizesSpec : Prop := ArrayStorageSizeSpec ∧ PointerStrideSpec

theorem storageSizesSpec : StorageSizesSpec := ⟨arrayStorageSizeSpec, pointerStrideSpec⟩

/-- `to_index` is an indices.jl primitive. Its laws include Bool rejection and
checked conversion of arbitrary-width integer values to the platform Int. -/
def UnsetIntegerFullSpec : Prop :=
  ∀ (α : Type) (toIndex : Bool → Int → Except Error I) (message : String),
    (∀ b value, toIndex b value =
      if b then .error (.argument message)
      else (JInt.convert .i64 value).mapError (fun _ => Error.inexact)) →
    ∀ (n : Nat) (slots : I → Option α) (b : Bool) (value : Int),
      (unsetindexInteger (fun value => slotLift (toIndex b value))
        (unsetindexInt (slotBounds n) slotRef slotUnset) () value).run slots =
      if b then (.error (.argument message), slots)
      else
        match (JInt.convert .i64 value).mapError (fun _ => Error.inexact) with
        | .error e => (.error e, slots)
        | .ok i =>
          if 1 ≤ i.val ∧ i.val ≤ (n : Int) then (.ok (), updateSlot slots i none)
          else (.error .bounds, slots)

theorem unsetIntegerFullSpec : UnsetIntegerFullSpec := by
  intro α toIndex message hlaw n slots b value
  cases b with
  | true =>
    simp [unsetindexInteger, hlaw, slotLift, ExceptT.run, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
  | false =>
    cases hc : (JInt.convert .i64 value).mapError (fun _ => Error.inexact) with
    | error e =>
      simp [unsetindexInteger, hlaw, hc, slotLift, ExceptT.run, ExceptT.bind,
        ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    | ok i =>
      by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int) <;>
        simp [unsetindexInteger, hlaw, hc, unsetindexInt, slotBounds, slotRef, slotUnset,
          slotLift, hb, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
          ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]

def slotGet (n : Nat) (i : I) : SlotM α α := do
  slotBounds n () i
  slotRead i

def ReadableSpec : Prop := ∀ (α : Type) (slots : I → Option α) (n : Nat) (i : I),
  (isassignedVector (m := Id) (fun (_ : Unit) j => decide (1 ≤ j.val ∧ j.val ≤ (n : Int)))
    (fun _ j _ => j) (fun j => (slots j).isSome) () i = true ↔
      ∃ x, (slotGet n i).run slots = (.ok x, slots)) ∧
  (¬ (1 ≤ i.val ∧ i.val ≤ (n : Int)) →
    (slotGet n i).run slots = (.error .bounds, slots)) ∧
  (1 ≤ i.val ∧ i.val ≤ (n : Int) →
    (do
      let _ ← unsetindexInt (slotBounds n) slotRef slotUnset () i
      slotRead i : SlotM α α).run slots =
        (.error .undefinedReference, updateSlot slots i none))

theorem readableSpec : ReadableSpec := by
  intro α slots n i
  by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int) <;> cases hs : slots i <;>
    simp [isassignedVector, slotGet, slotBounds, slotRead, hb, hs, unsetindexInt,
      slotRef, slotUnset, updateSlot, ExceptT.run, ExceptT.bind, ExceptT.pure,
      ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
  all_goals
    first
    | exact ⟨_, rfl⟩
    | intro x hx
      have hh := congrArg (fun p : Except Error α × (I → Option α) => p.1) hx
      cases hh

def LinearAccessComplete : Prop := LinearAccessSpec ∧ AssignmentSpec ∧ ReadableSpec

theorem linearAccessComplete : LinearAccessComplete :=
  ⟨linearAccessSpec, assignmentSpec, readableSpec⟩

abbrev ByteMemory := Nat → JInt .u8

/-- The documented memmove interface reads overlapping source bytes before writing. -/
def ByteMoveLaw (move : Nat → Nat → I → StateM ByteMemory Unit) : Prop :=
  ∀ (old : ByteMemory) (dest src : Nat) (bytes : I), 0 ≤ bytes.val →
    ∀ address, ((move dest src bytes).run old).2 address =
      if dest ≤ address ∧ address < dest + bytes.val.toNat
      then old (src + (address - dest)) else old address

def PointerCopySpec : Prop :=
  ∀ (N : Type) (value : N → Int) (multiply : N → I → I),
    (∀ n stride, 0 ≤ value n → 0 ≤ stride.val →
      value n * stride.val ≤ IntTy.i64.max →
      (multiply n stride).val = value n * stride.val) →
    ∀ (move : Nat → Nat → I → StateM ByteMemory Unit), ByteMoveLaw move →
    ∀ (old : ByteMemory) (dest src : Nat) (n : N) (stride : I),
      0 ≤ value n → 0 ≤ stride.val → value n * stride.val ≤ IntTy.i64.max →
      let result := (unsafeCopyPtr stride multiply move dest src n).run old
      result.1 = dest ∧
      (∀ k, k < (value n).toNat → ∀ j, j < stride.val.toNat →
        result.2 (dest + k * stride.val.toNat + j) =
          old (src + k * stride.val.toNat + j)) ∧
      (∀ address, address < dest ∨ dest + (value n).toNat * stride.val.toNat ≤ address →
        result.2 address = old address)

theorem unsafeCopyPtr_state_run (stride : I) (multiply : N → I → Bytes)
    (move : P → P → Bytes → StateM σ Unit) (dest src : P) (n : N) (state : σ) :
    (unsafeCopyPtr stride multiply move dest src n).run state =
      (dest, ((move dest src (multiply n stride)).run state).2) := by
  rfl

theorem pointerCopySpec : PointerCopySpec := by
  intro N value multiply hmul move hlaw old dest src n stride hn hs hmax result
  have hnonneg : 0 ≤ value n * stride.val := Int.mul_nonneg hn hs
  have hv := hmul n stride hn hs hmax
  have hbytes : (multiply n stride).val.toNat = (value n).toNat * stride.val.toNat := by
    rw [hv, Int.toNat_mul hn hs]
  have hm := hlaw old dest src (multiply n stride) (by rw [hv]; exact hnonneg)
  dsimp [result]
  rw [unsafeCopyPtr_state_run]
  refine ⟨rfl, ?_, ?_⟩
  · intro k hk j hj
    rw [hm, hbytes]
    have hle : (k + 1) * stride.val.toNat ≤ (value n).toNat * stride.val.toNat :=
      Nat.mul_le_mul_right _ hk
    rw [Nat.add_mul, Nat.one_mul] at hle
    rw [ite_eq_left (by constructor <;> omega)]
    congr 1
    omega
  · intro address ha
    rw [hm, hbytes, ite_eq_right (by omega)]

def AssignmentLinearArraySpec : Prop := ∀ (α : Type) (slots : I → Option α)
    (dims : List Nat) (bounds : List I → Bool) (linear : List Nat → List I → I),
  (∀ i, bounds [i] = decide (1 ≤ i.val ∧ i.val ≤ (dims.prod : Int))) →
  bounds [] = dims.all (fun d => d == 1) →
  (∀ i, linear dims [i] = i) → linear dims [] = one →
  ∀ i,
    (isassignedArray (m := Id) (fun (_ : Unit) js => bounds js) (fun _ => dims)
      linear (fun _ j _ => j) (fun j => (slots j).isSome) () [i] = true ↔
        1 ≤ i.val ∧ i.val ≤ (dims.prod : Int) ∧ ∃ x, slots i = some x) ∧
    (isassignedArray (m := Id) (fun (_ : Unit) js => bounds js) (fun _ => dims)
      linear (fun _ j _ => j) (fun j => (slots j).isSome) () [] = true ↔
        dims.all (fun d => d == 1) = true ∧ ∃ x, slots one = some x)

theorem assignmentLinearArraySpec : AssignmentLinearArraySpec := by
  intro α slots dims bounds linear hsingle hempty hlinear hzero i
  have h := (assignmentSpec α slots dims.prod i).2 (List Nat) dims bounds linear [i]
  have h0 := (assignmentSpec α slots dims.prod i).2 (List Nat) dims bounds linear []
  rw [hsingle, hlinear] at h
  rw [hempty, hzero] at h0
  exact ⟨by simpa only [decide_eq_true_eq, and_assoc] using h, h0⟩

def SafeStoreSpec : Prop := ∀ (α β : Type) (slots : I → Option α)
    (n : Nat) (i : I) (x : α) (v : β) (convert : β → Except Error α),
  1 ≤ i.val ∧ i.val ≤ (n : Int) →
  (safeSetindex1055 slotRefNew slotStore () x i).run slots =
    (.ok (), updateSlot slots i (some x)) ∧
  (safeSetindex1057 slotRefNew slotStore () x i).run slots =
    (.ok (), updateSlot slots i (some x)) ∧
  (safeSetindexConvert (fun v => slotLift (convert v))
    (safeSetindex1057 slotRefNew slotStore) () v i).run slots =
    match convert v with
    | .error e => (.error e, slots)
    | .ok y => (.ok (), updateSlot slots i (some y))

theorem safeStoreSpec : SafeStoreSpec := by
  intro α β slots n i x v convert _hb
  cases hc : convert v <;>
    simp [safeSetindex1055, safeSetindex1057, safeSetindexConvert, slotRefNew,
      slotStore, slotLift, hc, ExceptT.run, ExceptT.bind, ExceptT.pure,
      ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]

def AllLiteralContents : Prop := LiteralContents ∧ ConvertedLiteralContents

theorem allLiteralContents : AllLiteralContents := ⟨literalContents, convertedLiteralContents⟩

/-- A window copy reads the old source even when the address ranges overlap. -/
def copiedElements (old : Nat → Option α) (dest src count : Nat) : Nat → Option α :=
  fun address => if dest ≤ address ∧ address < dest + count
    then old (src + (address - dest)) else old address

def UnsafeArrayCopySpec : Prop :=
  ∀ (α OffD OffS N : Type) (destValue : OffD → Int) (srcValue : OffS → Int)
    (countValue : N → Int)
    (destReference : (Nat × Nat) → OffD → StateM (Nat → Option α) Nat)
    (srcReference : (Nat × Nat) → OffS → StateM (Nat → Option α) Nat)
    (copy : Nat → Nat → N → StateM (Nat → Option α) Unit),
    (∀ old a i, 1 ≤ destValue i ∧ destValue i ≤ (a.2 : Int) →
      (destReference a i).run old = (a.1 + (destValue i - 1).toNat, old)) →
    (∀ old a i, 1 ≤ srcValue i ∧ srcValue i ≤ (a.2 : Int) →
      (srcReference a i).run old = (a.1 + (srcValue i - 1).toNat, old)) →
    (∀ old dest src n, 0 ≤ countValue n →
      (copy dest src n).run old = ((), copiedElements old dest src (countValue n).toNat)) →
    ∀ (old : Nat → Option α) (dest src : Nat × Nat) (di : OffD) (si : OffS) (n : N),
      0 ≤ countValue n →
      (countValue n ≠ 0 →
        1 ≤ destValue di ∧ destValue di + countValue n - 1 ≤ (dest.2 : Int) ∧
        1 ≤ srcValue si ∧ srcValue si + countValue n - 1 ≤ (src.2 : Int)) →
      (unsafeCopyArray (fun n => countValue n == 0) destReference srcReference copy
        dest di src si n).run old =
      (dest, copiedElements old (dest.1 + (destValue di - 1).toNat)
        (src.1 + (srcValue si - 1).toNat) (countValue n).toNat)

theorem unsafeCopyArray_state_run (isZero : N → Bool)
    (destRef : D → OffD → StateM σ R) (srcRef : S → OffS → StateM σ R)
    (copy : R → R → N → StateM σ Unit)
    (dest : D) (di : OffD) (src : S) (si : OffS) (n : N) (old : σ) :
    (unsafeCopyArray isZero destRef srcRef copy dest di src si n).run old =
      if isZero n then (dest, old)
      else
        let d := (destRef dest di).run old
        let s := (srcRef src si).run d.2
        (dest, ((copy d.1 s.1 n).run s.2).2) := by
  cases hz : isZero n <;> simp only [unsafeCopyArray, hz, Bool.false_eq_true,
    ↓reduceIte]
  all_goals rfl

theorem unsafeArrayCopySpec : UnsafeArrayCopySpec := by
  intro α OffD OffS N destValue srcValue countValue destReference srcReference copy
    hdest hsrc hcopy old dest src di si n hn hvalid
  rw [unsafeCopyArray_state_run]
  by_cases hz : countValue n = 0
  · have he : copiedElements old (dest.1 + (destValue di - 1).toNat)
        (src.1 + (srcValue si - 1).toNat) (countValue n).toNat = old := by
      funext address
      simp only [copiedElements, hz, Int.toNat_zero, Nat.add_zero]
      rw [ite_eq_right (by omega)]
    rw [he]
    simp [hz]
  · have hb := hvalid hz
    have hd : 1 ≤ destValue di ∧ destValue di ≤ (dest.2 : Int) := ⟨hb.1, by omega⟩
    have hs : 1 ≤ srcValue si ∧ srcValue si ≤ (src.2 : Int) := ⟨hb.2.2.1, by omega⟩
    have hzero : (countValue n == 0) = false := by simp [hz]
    simp only [hzero, Bool.false_eq_true, ↓reduceIte]
    rw [hdest old dest di hd, hsrc old src si hs, hcopy _ _ _ n hn]

/-- Heap addresses let distinct arrays share arbitrary overlapping storage. -/
abbrev CopyM (α : Type) := ExceptT Error (StateM (Nat → Option α))

@[simp] theorem stateExcept_pure (x : β) (old : σ) :
    (pure x : ExceptT Error (StateM σ) β).run old = (.ok x, old) := rfl

@[simp] theorem stateExcept_bind (action : ExceptT Error (StateM σ) β)
    (next : β → ExceptT Error (StateM σ) γ) (old : σ) :
    (action >>= next).run old =
      match action.run old with
      | (.error e, state) => (.error e, state)
      | (.ok x, state) => (next x).run state := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action old with
  | mk r state =>
    cases r <;> rfl

@[simp] theorem stateExcept_throw (e : Error) (old : σ) :
    (throw e : ExceptT Error (StateM σ) β).run old = (.error e, old) := rfl

@[simp] theorem stateExcept_ite (p : Prop) [Decidable p]
    (yes no : ExceptT Error (StateM σ) β) (old : σ) :
    (if p then yes else no).run old = if p then yes.run old else no.run old := by
  split <;> rfl

/-- The memory.jl primitive copies a snapshot, including unassigned slots. -/
def MemoryCopyLaw (copy : Nat → Nat → I → CopyM α Unit) : Prop :=
  ∀ old dest src n, 0 ≤ n.val →
    (copy dest src n).run old =
      (.ok (), copiedElements old dest src n.val.toNat)

def copyBounds (value : Z → Int) (a : Nat × Nat) (i : Z) : CopyM α Unit :=
  fun old => (if 1 ≤ value i ∧ value i ≤ (a.2 : Int)
    then .ok () else .error .bounds, old)

def copyReference (a : Nat × Nat) (i : I) : CopyM α Nat :=
  fun old => (.ok (a.1 + (i.val - 1).toNat), old)

def copyInt (value : Z → Int) (i : Z) : CopyM α I :=
  fun old => (if IntTy.i64.min ≤ value i ∧ value i ≤ IntTy.i64.max
    then .ok (JInt.wrap .i64 (value i)) else .error .inexact, old)

def copyLength (a : Nat × Nat) : CopyM α I :=
  fun old => (.ok (JInt.wrap .i64 a.2), old)

@[simp] theorem copyBounds_run (value : Z → Int) (a : Nat × Nat) (i : Z)
    (old : Nat → Option α) :
    (copyBounds value a i).run old =
      (if 1 ≤ value i ∧ value i ≤ (a.2 : Int) then .ok () else .error .bounds, old) := rfl

@[simp] theorem copyReference_run (a : Nat × Nat) (i : I) (old : Nat → Option α) :
    (copyReference a i).run old = (.ok (a.1 + (i.val - 1).toNat), old) := rfl

@[simp] theorem copyInt_run (value : Z → Int) (i : Z) (old : Nat → Option α) :
    (copyInt value i).run old =
      (if IntTy.i64.min ≤ value i ∧ value i ≤ IntTy.i64.max
        then .ok (JInt.wrap .i64 (value i)) else .error .inexact, old) := rfl

@[simp] theorem copyLength_run (a : Nat × Nat) (old : Nat → Option α) :
    (copyLength a).run old = (.ok (JInt.wrap .i64 a.2), old) := rfl

/-- Independent window semantics: validation precedes every write. -/
def checkedCopyResult (old : Nat → Option α) (dest src : Nat × Nat)
    (di si n : Int) : Except Error (Nat × Nat) × (Nat → Option α) :=
  if n = 0 then (.ok dest, old)
  else if n < 0 then
    (.error (.argument "Number of elements to copy must be non-negative."), old)
  else if 1 ≤ di ∧ di + n - 1 ≤ (dest.2 : Int) ∧
      1 ≤ si ∧ si + n - 1 ≤ (src.2 : Int) then
    (.ok dest, copiedElements old (dest.1 + (di - 1).toNat)
      (src.1 + (si - 1).toNat) n.toNat)
  else (.error .bounds, old)

theorem copy_remaining (len : Nat) (i : Int) (hlen : len < 2 ^ 63)
    (hi : 1 ≤ i ∧ i ≤ (len : Int)) :
    (JInt.wrap .i64 ((JInt.wrap .i64 len).val - i) + one).val =
      (len : Int) - i + 1 := by
  have hl : (JInt.wrap .i64 len).val = len := by
    change wrapInt .i64 (len : Int) = len
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
    omega
  have hs : (JInt.wrap .i64 ((len : Int) - i)).val = (len : Int) - i := by
    change wrapInt .i64 ((len : Int) - i) = (len : Int) - i
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
    omega
  change wrapInt .i64 ((JInt.wrap .i64 ((JInt.wrap .i64 len).val - i)).val + one.val) = _
  rw [hl, hs]
  change wrapInt .i64 ((len : Int) - i + 1) = _
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
  omega

def CheckedCopySpec : Prop :=
  ∀ (α OffD OffS Count : Type) (dv : OffD → Int) (sv : OffS → Int) (nv : Count → Int)
    (copy : Nat → Nat → I → CopyM α Unit), MemoryCopyLaw copy →
    ∀ (old : Nat → Option α) (dest src : Nat × Nat) (di : OffD) (si : OffS) (n : Count),
    dest.2 < 2 ^ 63 → src.2 < 2 ^ 63 →
    let impl := copytoImpl nv copyLength copyLength (copyBounds dv) (copyBounds sv)
      (fun len i => JInt.wrap .i64 (len.val - dv i))
      (fun len i => JInt.wrap .i64 (len.val - sv i))
      (copyInt dv) (copyInt sv) (copyInt nv) copyReference copyReference copy
    ∀ operation ∈ [impl, copyto288 impl, copyto290 impl, copyto292 impl, copyto296 impl],
      (operation dest di src si n).run old = checkedCopyResult old dest src (dv di) (sv si) (nv n)

theorem checkedCopySpec : CheckedCopySpec := by
  intro α OffD OffS Count dv sv nv copy hcopy old dest src di si n hd hs impl operation hop
  have core : (impl dest di src si n).run old =
      checkedCopyResult old dest src (dv di) (sv si) (nv n) := by
    by_cases hz : nv n = 0
    · simp [impl, copytoImpl, checkedCopyResult, hz]
    by_cases hn : nv n < 0
    · have hp : ¬nv n > 0 := by omega
      simp [impl, copytoImpl, checkedCopyResult, hz, hn, hp]
    have hnpos : nv n > 0 := by omega
    by_cases hdi : 1 ≤ dv di ∧ dv di ≤ (dest.2 : Int)
    · have hdr := copy_remaining dest.2 (dv di) hd hdi
      change wrapInt .i64 ((JInt.wrap .i64 ((JInt.wrap .i64 (dest.2 : Int)).val - dv di)).val + one.val) =
        (dest.2 : Int) - dv di + 1 at hdr
      by_cases hdn : nv n ≤ (dest.2 : Int) - dv di + 1
      · by_cases hsi : 1 ≤ sv si ∧ sv si ≤ (src.2 : Int)
        · have hsr := copy_remaining src.2 (sv si) hs hsi
          change wrapInt .i64 ((JInt.wrap .i64 ((JInt.wrap .i64 (src.2 : Int)).val - sv si)).val + one.val) =
            (src.2 : Int) - sv si + 1 at hsr
          by_cases hsn : nv n ≤ (src.2 : Int) - sv si + 1
          · have hvalid : 1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int) := by omega
            have hdc : IntTy.i64.min ≤ dv di ∧ dv di ≤ IntTy.i64.max := by
              simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
            have hsc : IntTy.i64.min ≤ sv si ∧ sv si ≤ IntTy.i64.max := by
              simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
            have hnc : IntTy.i64.min ≤ nv n ∧ nv n ≤ IntTy.i64.max := by
              simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
            have hdv : (JInt.wrap .i64 (dv di)).val = dv di := wrapInt_of_inRange _ _ hdc
            have hsv : (JInt.wrap .i64 (sv si)).val = sv si := wrapInt_of_inRange _ _ hsc
            have hnv : (JInt.wrap .i64 (nv n)).val = nv n := wrapInt_of_inRange _ _ hnc
            simp only [checkedCopyResult, hz, hn, hvalid, ite_false]
            simp [impl, copytoImpl, hz, hnpos,
              hdi, hsi, hdc, hsc, hnc, hdr, hsr, hdv, hsv,
              Int.not_lt_of_ge hdn, Int.not_lt_of_ge hsn]
            change (let result := (copy (dest.1 + ((dv di).toNat - 1))
                (src.1 + ((sv si).toNat - 1)) (JInt.wrap .i64 (nv n))).run old
              (result.1.map (fun _ => dest), result.2)) = _
            rw [hcopy old _ _ _ (by rw [hnv]; omega)]
            simp only [hnv, Except.map]
          · have hv : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
            simp only [checkedCopyResult, hz, hn, hv, ite_false]
            simp [impl, copytoImpl, hz, hnpos,
              hdi, hsi, hdr, hsr, Int.not_lt_of_ge hdn, Int.lt_of_not_ge hsn]
        · have hv : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
          simp only [checkedCopyResult, hz, hn, hv, ite_false]
          simp [impl, copytoImpl, hz, hnpos,
            hdi, hsi, hdr, Int.not_lt_of_ge hdn]
      · have hv : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
        simp only [checkedCopyResult, hz, hn, hv, ite_false]
        simp [impl, copytoImpl, hz, hnpos, hdi, hdr, Int.lt_of_not_ge hdn]
    · have hv : ¬(1 ≤ dv di ∧ dv di + nv n - 1 ≤ (dest.2 : Int) ∧
                1 ≤ sv si ∧ sv si + nv n - 1 ≤ (src.2 : Int)) := by omega
      simp only [checkedCopyResult, hz, hn, hv, ite_false]
      simp [impl, copytoImpl, hz, hnpos, hdi]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> exact core

def WholeCopySpec : Prop :=
  ∀ (α : Type) (copy : Nat → Nat → I → CopyM α Unit), MemoryCopyLaw copy →
    ∀ (old : Nat → Option α) (dest src : Nat × Nat),
    dest.2 < 2 ^ 63 → src.2 < 2 ^ 63 →
    let impl := copytoImpl (fun i : I => i.val) copyLength copyLength
      (copyBounds (fun i : I => i.val)) (copyBounds (fun i : I => i.val))
      (fun len i => JInt.wrap .i64 (len.val - i.val))
      (fun len i => JInt.wrap .i64 (len.val - i.val))
      (copyInt (fun i : I => i.val)) (copyInt (fun i : I => i.val))
      (copyInt (fun i : I => i.val)) copyReference copyReference copy
    let whole := copyto2arg (fun _ => pure one) (fun _ => pure one) copyLength (copyto288 impl)
    ∀ operation ∈ [whole, copyto325 whole, copyto326 whole, copyto327 whole,
        copyto330 whole, copyto331 whole, copyto332 whole],
      (operation dest src).run old =
        if src.2 ≤ dest.2 then (.ok dest, copiedElements old dest.1 src.1 src.2)
        else (.error .bounds, old)

theorem wholeCopySpec : WholeCopySpec := by
  intro α copy hcopy old dest src hd hs impl whole operation hop
  have hlen : (JInt.wrap .i64 (src.2 : Int)).val = src.2 := by
    change wrapInt .i64 (src.2 : Int) = src.2
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hc := checkedCopySpec α I I I (fun i => i.val) (fun i => i.val) (fun i => i.val)
    copy hcopy old dest src one one (JInt.wrap .i64 src.2) hd hs
    (copyto288 impl) (by simp [impl])
  have hc' : (whole dest src).run old =
      checkedCopyResult old dest src 1 1 (src.2 : Int) := by
    simpa only [whole, copyto2arg, stateExcept_bind, stateExcept_pure,
      copyLength_run, hlen, show one.val = 1 from rfl] using hc
  have result : (whole dest src).run old =
      if src.2 ≤ dest.2 then (.ok dest, copiedElements old dest.1 src.1 src.2)
      else (.error .bounds, old) := by
    rw [hc']
    by_cases hz : src.2 = 0
    · simp only [checkedCopyResult, hz]
      simp
      apply congrArg (fun f => (Except.ok dest, f))
      funext address
      simp [copiedElements]
      omega
    · have hp : ¬(src.2 : Int) < 0 := by omega
      have heq : 1 + (src.2 : Int) - 1 = src.2 := by omega
      simp [checkedCopyResult, hz, hp, heq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact result

theorem fill_loop {K α : Type} [DecidableEq K] (keys : List K)
    (step : K → ExceptT Error (StateM (K → Option α)) Unit) (x : α)
    (hlaw : ∀ old i, i ∈ keys →
      (step i).run old = (.ok (), fun j => if j = i then some x else old j))
    (old : K → Option α) :
    (forIn keys () (fun i _ => do step i; pure (ForInStep.yield ()))).run old =
      (.ok (), fun j => if j ∈ keys then some x else old j) := by
  induction keys generalizing old with
  | nil =>
    simp [ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.pure, Pure.pure]
  | cons i keys ih =>
    have hstep := hlaw old i (by simp)
    have htail : ∀ old i, i ∈ keys →
        (step i).run old = (.ok (), fun j => if j = i then some x else old j) := by
      intro old j hj
      exact hlaw old j (by simp [hj])
    simp only [List.forIn_cons, stateExcept_bind, stateExcept_pure, hstep]
    rw [ih htail]
    congr 1
    funext j
    by_cases hj : j = i <;> simp [List.mem_cons, hj]

def FillContentsSpec : Prop :=
  ∀ (α β : Type) (n : Nat) (keys : List I),
    (∀ j, j ∈ keys ↔ 1 ≤ j.val ∧ j.val ≤ (n : Int)) →
    ∀ (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
      (v : β) (x : α) (old : I → Option α),
    let set := setindexScalar (fun _ : α => true) id
      (fun x => (pure x : SlotM α α))
      (setindexTyped (slotBounds n) slotRefNew slotStore)
    let typed := fillTyped (fun _ : Unit => (pure keys : SlotM α (List I))) set
    (typed () x).run old =
      (.ok (), fun j => if 1 ≤ j.val ∧ j.val ≤ (n : Int) then some x else old j) ∧
    (fillBang already asTyped (fun v => slotLift (convert v)) typed () v).run old =
      match (if already v then .ok (asTyped v) else convert v) with
      | .error e => (.error e, old)
      | .ok y =>
        (.ok (), fun j => if 1 ≤ j.val ∧ j.val ≤ (n : Int) then some y else old j)

theorem fillContentsSpec : FillContentsSpec := by
  intro α β n keys hkeys already asTyped convert v x old set typed
  have htyped : ∀ (y : α) (state : I → Option α), (typed () y).run state =
      (.ok (), fun j => if 1 ≤ j.val ∧ j.val ≤ (n : Int) then some y else state j) := by
    intro y state
    have hstep : ∀ old i, i ∈ keys →
        (set () y i).run old = (.ok (), updateSlot old i (some y)) := by
      intro old i hi
      have hb := (hkeys i).mp hi
      simp [set, setindexScalar, setindexTyped, slotBounds, slotRefNew, slotStore, hb,
        ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    have hloop := fill_loop keys (set () y) y hstep state
    simp only [hkeys] at hloop
    simp only [typed, fillTyped, stateExcept_bind, stateExcept_pure]
    rw [hloop]
  refine ⟨htyped x old, ?_⟩
  cases ha : already v with
  | true =>
    simpa only [fillBang, ha, ite_true, Bool.true_eq, stateExcept_bind, stateExcept_pure]
      using htyped (asTyped v) old
  | false =>
    cases hc : convert v with
    | error e =>
      simp [fillBang, ha, hc, slotLift, ExceptT.run, ExceptT.bind,
        ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure,
        Bind.bind, Pure.pure]
    | ok y =>
      have hlift : (slotLift (.ok y) : SlotM α α).run old = (.ok y, old) := rfl
      simpa only [fillBang, ha, Bool.false_eq_true, ite_false, hc,
        stateExcept_bind, hlift] using htyped y old

/-- Allocating new memory cannot change an existing object or alias its slots. -/
def FreshMemoryLaw (allocate : Nat → I → CopyM α Nat) : Prop :=
  ∀ old src n, 0 ≤ n.val →
    ∃ base next, (allocate src n).run old = (.ok base, next) ∧
      (base + n.val.toNat ≤ src ∨ src + n.val.toNat ≤ base) ∧
      (∀ address, address < base ∨ base + n.val.toNat ≤ address → next address = old address)

def CopyArraySpec : Prop :=
  ∀ (α : Type) (allocate : Nat → I → CopyM α Nat)
    (copy : Nat → Nat → I → CopyM α Unit),
    FreshMemoryLaw allocate → MemoryCopyLaw copy →
    ∀ (old : Nat → Option α) (a : Nat × List Nat), a.2.prod < 2 ^ 63 →
    let result := (copyArray (fun a => pure a.1)
      (fun a => pure (JInt.wrap .i64 a.2.prod)) allocate (fun mem => pure mem) copy
      (fun a => pure a.2) (fun ref dims => pure (ref, dims)) a).run old
    ∃ fresh, result.1 = .ok (fresh, a.2) ∧
      (fresh + a.2.prod ≤ a.1 ∨ a.1 + a.2.prod ≤ fresh) ∧
      ∀ address, result.2 address =
        if fresh ≤ address ∧ address < fresh + a.2.prod
        then old (a.1 + (address - fresh)) else old address

theorem copyArraySpec : CopyArraySpec := by
  intro α allocate copy ha hc old a hn result
  have hlen : (JInt.wrap .i64 (a.2.prod : Int)).val = a.2.prod := by
    change wrapInt .i64 (a.2.prod : Int) = a.2.prod
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  obtain ⟨fresh, next, halloc, hdisjoint, hframe⟩ :=
    ha old a.1 (JInt.wrap .i64 a.2.prod) (by rw [hlen]; omega)
  have hrun : result = (.ok (fresh, a.2), copiedElements next fresh a.1 a.2.prod) := by
    dsimp only [result]
    simp only [copyArray, stateExcept_bind, stateExcept_pure, halloc,
      hc next fresh a.1 (JInt.wrap .i64 a.2.prod) (by rw [hlen]; omega), hlen, Int.toNat_natCast]
  rw [hlen] at hdisjoint hframe
  refine ⟨fresh, ?_, hdisjoint, ?_⟩
  · rw [hrun]
  · intro address
    rw [hrun]
    simp only [copiedElements]
    split
    · rename_i haddress
      apply hframe
      rcases hdisjoint with hbefore | hafter <;> omega
    · rename_i hout
      apply hframe
      omega

def objectRef {A R D : Type} (a : A) : StateM (A → R × D) R :=
  fun objects => ((objects a).1, objects)

def objectSize {A R D : Type} (a : A) : StateM (A → R × D) D :=
  fun objects => ((objects a).2, objects)

def objectSetRef {A R D : Type} [DecidableEq A] (a : A) (ref : R) : StateM (A → R × D) Unit :=
  fun objects => ((), fun k => if k = a then (ref, (objects k).2) else objects k)

def objectSetSize {A R D : Type} [DecidableEq A] (a : A) (dims : D) : StateM (A → R × D) Unit :=
  fun objects => ((), fun k => if k = a then ((objects k).1, dims) else objects k)

def TakeFieldsSpec : Prop :=
  ∀ (A R D : Type) [DecidableEq A] [DecidableEq R] [DecidableEq D]
    (objects : A → R × D) (dst src : A),
    (takeBang objectRef (fun x y => x == y) objectSetRef objectSize
      (fun x y => x == y) objectSetSize dst src).run objects =
      (dst, fun k => if k = dst then objects src else objects k)

theorem takeFieldsSpec : TakeFieldsSpec := by
  intro A R D _ _ _ objects dst src
  by_cases ha : dst = src
  · subst src
    simp [takeBang, objectRef, objectSize,
      StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    apply congrArg (fun f => (dst, f))
    funext k
    split <;> simp_all
  · have hrev : src ≠ dst := Ne.symm ha
    by_cases hr : (objects dst).1 = (objects src).1 <;>
      by_cases hs : (objects dst).2 = (objects src).2 <;>
      simp [takeBang, objectRef, objectSize, objectSetRef, objectSetSize, hrev, hr, hs,
        StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    all_goals
      apply congrArg (fun f => (dst, f))
      funext k
      by_cases hk : k = dst <;> simp_all
    all_goals exact Prod.ext hr hs

def FreshArray {B α : Type} (shape : B → List I) (slots : B → List (Option α))
    (dims : List I) (a : B) : Prop :=
  shape a = dims ∧ slots a = List.replicate ((dims.map (fun d : I => d.val)).prod.toNat) none

def SimilarShapeSpec : Prop :=
  ∀ (α A B : Type) (shape : B → List I) (slots : B → List (Option α))
    (allocate : List I → Except Error B),
    (∀ dims, (∀ d ∈ dims, 0 ≤ d.val) → (dims.map (fun d => d.val)).prod ≤ IntTy.i64.max →
      ∃ b, allocate dims = .ok b ∧ FreshArray shape slots dims b) →
    (∀ dims, (∃ d ∈ dims, d.val < 0) →
      ∃ message, allocate dims = .error (.argument message)) →
    ∀ (size : A → I → Except Error I) (a : A) (n m : I) (dims : List I),
    size a one = .ok n → size a (JInt.wrap .i64 2) = .ok m →
    (0 ≤ n.val → ∀ result ∈
        [similar414 size (fun n => allocate [n]) a,
         similar416 size (fun n => allocate [n]) a,
         similar418 (fun n => allocate [n]) a n],
      ∃ b, result = .ok b ∧ FreshArray shape slots [n] b) ∧
    (0 ≤ n.val → 0 ≤ m.val → n.val * m.val ≤ IntTy.i64.max →
      ∀ result ∈ [similar415 size (fun n m => allocate [n, m]) a,
        similar417 size (fun n m => allocate [n, m]) a],
      ∃ b, result = .ok b ∧ FreshArray shape slots [n, m] b) ∧
    ((∀ d ∈ dims, 0 ≤ d.val) → (dims.map (fun d => d.val)).prod ≤ IntTy.i64.max →
      ∀ result ∈ [similar419 allocate a dims, similar420 allocate a dims,
        similar421 (similar420 allocate a) dims],
      ∃ b, result = .ok b ∧ FreshArray shape slots dims b) ∧
    ((∃ d ∈ dims, d.val < 0) →
      ∀ result ∈ [similar419 allocate a dims, similar420 allocate a dims,
        similar421 (similar420 allocate a) dims],
      ∃ message, result = .error (.argument message)) ∧
    (n.val < 0 → ∃ message, similar418 (fun n => allocate [n]) a n = .error (.argument message))

theorem similarShapeSpec : SimilarShapeSpec := by
  intro α A B shape slots allocate hgood hnegative size a n m dims hn hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnonneg result hr
    have h := hgood [n] (by simpa using hnonneg) (by simpa using n.property.2)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa [similar414, hn, Bind.bind, Except.bind] using h
    · simpa [similar416, hn, Bind.bind, Except.bind] using h
    · exact h
  · intro hn0 hm0 hprod result hr
    have h := hgood [n, m] (by simpa using And.intro hn0 hm0) (by simpa using hprod)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa [similar415, hn, hm, Bind.bind, Except.bind] using h
    · simpa [similar417, hn, hm, Bind.bind, Except.bind] using h
  · intro hnonneg hprod result hr
    have h := hgood dims hnonneg hprod
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact h
  · intro hneg result hr
    have h := hnegative dims hneg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact h
  · intro hneg
    exact hnegative [n] ⟨n, by simp, hneg⟩

def stateExceptLift {σ β : Type} (value : Except Error β) : ExceptT Error (StateM σ) β :=
  fun state => (value, state)

@[simp] theorem stateExceptLift_run (value : Except Error β) (old : σ) :
    (stateExceptLift value).run old = (value, old) := rfl

/-- The AbstractArray setter is an extensible interface from abstractarray.jl.
The concrete Array instance is additionally checked in FillContentsSpec. -/
def AbstractFillSpec : Prop :=
  ∀ (α β A K : Type) [DecidableEq K] (indices : A → List K)
    (set : A → α → K → ExceptT Error (StateM (K → Option α)) Unit),
    (∀ old a x i, i ∈ indices a →
      (set a x i).run old = (.ok (), fun j => if j = i then some x else old j)) →
    ∀ (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
      (a : A) (v : β) (x : α) (old : K → Option α),
    let typed := fillTyped (fun a => (pure (indices a) : ExceptT Error (StateM (K → Option α)) (List K))) set
    (typed a x).run old =
      (.ok a, fun j => if j ∈ indices a then some x else old j) ∧
    (fillBang already asTyped (fun v => stateExceptLift (convert v)) typed a v).run old =
      match (if already v then .ok (asTyped v) else convert v) with
      | .error e => (.error e, old)
      | .ok y => (.ok a, fun j => if j ∈ indices a then some y else old j)

theorem abstractFillSpec : AbstractFillSpec := by
  intro α β A K _ indices set hset already asTyped convert a v x old typed
  have htyped : ∀ (y : α) (state : K → Option α), (typed a y).run state =
      (.ok a, fun j => if j ∈ indices a then some y else state j) := by
    intro y state
    have hloop := fill_loop (indices a) (set a y) y (fun old i hi => hset old a y i hi) state
    simp only [typed, fillTyped, stateExcept_bind, stateExcept_pure]
    rw [hloop]
  refine ⟨htyped x old, ?_⟩
  cases ha : already v with
  | true =>
    simpa only [fillBang, ha, ite_true, Bool.true_eq, stateExcept_bind, stateExcept_pure]
      using htyped (asTyped v) old
  | false =>
    cases hc : convert v with
    | error e =>
      simp only [fillBang, ha, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc]
    | ok y =>
      simpa only [fillBang, ha, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc] using htyped y old

def CompleteFillSpec : Prop := FillContentsSpec ∧ AbstractFillSpec

theorem completeFillSpec : CompleteFillSpec := ⟨fillContentsSpec, abstractFillSpec⟩

def ByteFillSpec : Prop :=
  ∀ (Byte Z : Type) (memset : Nat → Byte → JInt .u64 → CopyM Byte Unit),
    (∀ old ptr x count, (memset ptr x count).run old =
      (.ok (), fun address => if ptr ≤ address ∧ address < ptr + count.val.toNat
        then some x else old address)) →
    ∀ (already : Z → Bool) (asTyped : Z → Byte) (convert : Z → Except Error Byte)
      (a : Nat × Nat) (v : Z) (old : Nat → Option Byte), a.2 < 2 ^ 63 →
    (fillBytes (fun a => pure a) (fun _ => pure ()) (fun ref => pure ref.1)
      already asTyped (fun v => stateExceptLift (convert v))
      (fun a => pure (JInt.wrap .i64 a.2)) memset (fun _ => pure ()) a v).run old =
      match (if already v then .ok (asTyped v) else convert v) with
      | .error e => (.error e, old)
      | .ok x =>
        (.ok a, fun address => if a.1 ≤ address ∧ address < a.1 + a.2
          then some x else old address)

theorem byteFillSpec : ByteFillSpec := by
  intro Byte Z memset hmemset already asTyped convert a v old hn
  have hlen : (JInt.wrap .i64 (a.2 : Int)).val = a.2 := by
    change wrapInt .i64 (a.2 : Int) = a.2
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hcount : (JInt.rem .u64 (JInt.wrap .i64 (a.2 : Int))).val.toNat = a.2 := by
    have hc : (JInt.rem .u64 (JInt.wrap .i64 (a.2 : Int))).val = a.2 := by
      change wrapInt .u64 (JInt.wrap .i64 (a.2 : Int)).val = a.2
      rw [hlen]
      apply wrapInt_of_inRange
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega
    rw [hc, Int.toNat_natCast]
  cases ha : already v with
  | true =>
    simp only [fillBytes, ha, ite_true, stateExcept_bind, stateExcept_pure,
      hmemset, hcount]
  | false =>
    cases hc : convert v <;>
      simp only [fillBytes, ha, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExcept_pure, stateExceptLift_run, hc, hmemset, hcount]

/-- Fresh array handles retain their type and dimensions while stores change only slots. -/
abbrev arrayShapeFiller {A α : Type} (shape : A → List Nat) (indices : List Nat → List I) :=
  fillBang (fun _ : α => true) id (fun x => (pure x : SlotM α α))
    (fillTyped (fun a => (pure (indices (shape a)) : SlotM α (List I)))
      (fun a x i => do
        let _ ← setindexScalar (fun _ : α => true) id (fun x => (pure x : SlotM α α))
          (setindexTyped (fun a i => slotBounds (shape a).prod () i)
            (fun _ i checked => slotRefNew () i checked) slotStore) a x i
        pure ()))

abbrev constructorFiller {α : Type} (indices : List Nat → List I) :=
  arrayShapeFiller (α := α) id indices

def filledShape (old : I → Option α) (dims : List Nat) (x : α) : I → Option α :=
  fun j => if 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int) then some x else old j

theorem arrayShapeFiller_run {A α : Type} (shape : A → List Nat)
    (indices : List Nat → List I)
    (hindices : ∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int))
    (a : A) (hdims : (shape a).prod < 2 ^ 63) (x : α) (old : I → Option α) :
    (arrayShapeFiller shape indices a x).run old =
      (.ok a, filledShape old (shape a) x) := by
  let step := fun i => do
    let _ ← setindexScalar (fun _ : α => true) id (fun x => (pure x : SlotM α α))
      (setindexTyped (fun a i => slotBounds (shape a).prod () i)
        (fun _ i checked => slotRefNew () i checked) slotStore) a x i
    pure ()
  have hs : ∀ state i, i ∈ indices (shape a) →
      (step i).run state = (.ok (), fun j => if j = i then some x else state j) := by
    intro state i hi
    have hb := (hindices (shape a) hdims i).mp hi
    simp [step, setindexScalar, setindexTyped, slotBounds, slotRefNew, slotStore,
      hb, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure]
    rfl
  have hloop := fill_loop (indices (shape a)) step x hs old
  simp only [hindices (shape a) hdims] at hloop
  simp only [arrayShapeFiller, fillBang, ite_true, fillTyped,
    stateExcept_bind, stateExcept_pure]
  simp only [step, id_eq] at hloop ⊢
  rw [hloop]
  rfl

theorem constructorFiller_run (indices : List Nat → List I)
    (hindices : ∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int))
    (dims : List Nat) (hdims : dims.prod < 2 ^ 63) (x : α) (old : I → Option α) :
    (constructorFiller indices dims x).run old = (.ok dims, filledShape old dims x) :=
  arrayShapeFiller_run id indices hindices dims hdims x old

/-- Successful runtime allocation preserves dimension values and valid storage size. -/
def AllocationShapeLaw (value : Z → Int)
    (allocate : List Z → SlotM α (List Nat)) : Prop :=
  ∀ old dims shape fresh, (allocate dims).run old = (.ok shape, fresh) →
    shape = dims.map (fun d => (value d).toNat) ∧ shape.prod < 2 ^ 63

def FillConstructorSpec : Prop :=
  ∀ (α Z : Type) (value : Z → Int) (allocate : List Z → SlotM α (List Nat)),
    AllocationShapeLaw value allocate →
    ∀ (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (v : α) (dims : List Z) (old : I → Option α),
    ∀ operation ∈ [fill585 allocate (constructorFiller indices),
      fill587 allocate (constructorFiller indices),
      fillVarargs (fill585 allocate (constructorFiller indices)),
      fill586 (similar421 (similar420 allocate ())) (constructorFiller indices)],
    (operation v dims).run old =
      match (allocate dims).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok _, fresh) =>
        let shape := dims.map (fun d => (value d).toNat)
        (.ok shape, filledShape fresh shape v)

theorem fillConstructorSpec : FillConstructorSpec := by
  intro α Z value allocate halloc indices hindices v dims old operation hop
  have hcore : (fill585 allocate (constructorFiller indices) v dims).run old =
      match (allocate dims).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok _, fresh) =>
        let shape := dims.map (fun d => (value d).toNat)
        (.ok shape, filledShape fresh shape v) := by
    cases ha : (allocate dims).run old with
    | mk result fresh =>
      cases result with
      | error e => simp only [fill585, stateExcept_bind, ha]
      | ok shape =>
        obtain ⟨hshape, hn⟩ := halloc old dims shape fresh ha
        simp only [fill585, stateExcept_bind, stateExcept_pure, ha]
        rw [constructorFiller_run indices hindices shape hn v fresh]
        simp only [hshape]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;> exact hcore

def dimensionArgument (d : Sum Z Z) : Z :=
  match d with
  | .inl integer => toDimInteger integer
  | .inr endpoint => toDimOneTo id endpoint

def MixedFillConstructorSpec : Prop :=
  ∀ (α Z : Type) (value : Z → Int) (allocate : List Z → SlotM α (List Nat)),
    AllocationShapeLaw value allocate →
    ∀ (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (v : α) (dims : List (Sum Z Z)) (old : I → Option α),
    ∀ operation ∈ [fillMixedDims dimensionArgument
      (fill585 allocate (constructorFiller indices)),
      fillVarargs (fillMixedDims dimensionArgument
        (fill585 allocate (constructorFiller indices)))],
    (operation v dims).run old =
      match (allocate (dims.map (fun d => d.elim id id))).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok _, fresh) =>
        let shape := dims.map (fun d => (value (d.elim id id)).toNat)
        (.ok shape, filledShape fresh shape v)

theorem mixedFillConstructorSpec : MixedFillConstructorSpec := by
  intro α Z value allocate halloc indices hindices v dims old operation hop
  have hmap : dims.map dimensionArgument = dims.map (fun d => d.elim id id) := by
    apply List.map_congr_left
    intro d _
    cases d <;> rfl
  have hc := fillConstructorSpec α Z value allocate halloc indices hindices v
    (dims.map (fun d => d.elim id id)) old
    (fill585 allocate (constructorFiller indices)) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl <;>
    simpa only [fillMixedDims, fillVarargs, hmap, List.map_map, Function.comp_def] using hc

def validAllocationDimensions (value : Z → Int) (dims : List Z) : Prop :=
  (∀ d ∈ dims, 0 ≤ value d ∧ value d ≤ IntTy.i64.max) ∧
    (dims.map value).prod ≤ IntTy.i64.max

def CheckedAllocationLaw (value : Z → Int)
    (allocate : List Z → SlotM α (List Nat)) : Prop :=
  AllocationShapeLaw value allocate ∧
  (∀ old dims, validAllocationDimensions value dims →
    ∃ fresh, (allocate dims).run old = (.ok (dims.map (fun d => (value d).toNat)), fresh)) ∧
  (∀ old dims, (∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
    (∃ d ∈ dims, value d < 0) →
    ∃ message, (allocate dims).run old = (.error (.argument message), old)) ∧
  (∀ old dims, (∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
    (allocate dims).run old = (.error .inexact, old))

def DocumentedFillDimensionsSpec : Prop :=
  ∀ (α Z : Type) (value : Z → Int) (allocate : List Z → SlotM α (List Nat)),
    CheckedAllocationLaw value allocate →
    ∀ (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (v : α) (dims : List Z) (old : I → Option α),
    let operations := [fill585 allocate (constructorFiller indices),
      fill587 allocate (constructorFiller indices),
      fillVarargs (fill585 allocate (constructorFiller indices)),
      fill586 (similar421 (similar420 allocate ())) (constructorFiller indices)]
    (validAllocationDimensions value dims →
      ∃ fresh, ∀ operation ∈ operations,
        (operation v dims).run old =
          (.ok (dims.map (fun d => (value d).toNat)),
            filledShape fresh (dims.map (fun d => (value d).toNat)) v)) ∧
    ((∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
      (∃ d ∈ dims, value d < 0) →
      ∃ message, ∀ operation ∈ operations,
        (operation v dims).run old = (.error (.argument message), old)) ∧
    ((∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
      ∀ operation ∈ operations, (operation v dims).run old = (.error .inexact, old))

theorem documentedFillDimensionsSpec : DocumentedFillDimensionsSpec := by
  intro α Z value allocate halloc indices hindices v dims old operations
  have hc := fillConstructorSpec α Z value allocate halloc.1 indices hindices v dims old
  refine ⟨?_, ?_, ?_⟩
  · intro hvalid
    obtain ⟨fresh, ha⟩ := halloc.2.1 old dims hvalid
    refine ⟨fresh, ?_⟩
    intro operation hop
    have h := hc operation hop
    simpa only [ha] using h
  · intro hrepresentable hnegative
    obtain ⟨message, ha⟩ := halloc.2.2.1 old dims hrepresentable hnegative
    refine ⟨message, ?_⟩
    intro operation hop
    have h := hc operation hop
    simpa only [ha] using h
  · intro hout operation hop
    have ha := halloc.2.2.2 old dims hout
    have h := hc operation hop
    simpa only [ha] using h

/-- A non-OneTo range axis selects the generic similar interface from abstractarray.jl. -/
inductive ConstructorAxis (Z : Type) where
  | integer : Z → ConstructorAxis Z
  | oneTo : Z → ConstructorAxis Z
  | range : Z → Z → ConstructorAxis Z

def unsupportedAxis : ConstructorAxis Z → Prop
  | .range _ _ => True
  | _ => False

def UnsupportedFillAxesSpec : Prop :=
  ∀ (α Z : Type)
    (similarAxes : List (ConstructorAxis Z) → SlotM α (List Nat)),
    (∀ old dims, (∃ d ∈ dims, unsupportedAxis d) →
      (similarAxes dims).run old = (.error (.method "similar"), old)) →
    ∀ (indices : List Nat → List I) (v : α) (dims : List (ConstructorAxis Z))
      (old : I → Option α), (∃ d ∈ dims, unsupportedAxis d) →
    (fill586 similarAxes (constructorFiller indices) v dims).run old =
      (.error (.method "similar"), old) ∧
    (fillVarargs (fill586 similarAxes (constructorFiller indices)) v dims).run old =
      (.error (.method "similar"), old)

theorem unsupportedFillAxesSpec : UnsupportedFillAxesSpec := by
  intro α Z similarAxes hsimilar indices v dims old haxis
  have hs := hsimilar old dims haxis
  simp only [fill586, fillVarargs, stateExcept_bind, hs, and_self]

def CompleteFillDimensionsSpec : Prop :=
  DocumentedFillDimensionsSpec ∧ MixedFillConstructorSpec ∧ UnsupportedFillAxesSpec

theorem completeFillDimensionsSpec : CompleteFillDimensionsSpec :=
  ⟨documentedFillDimensionsSpec, mixedFillConstructorSpec, unsupportedFillAxesSpec⟩

def TaggedAllocationShapeLaw (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)) : Prop :=
  ∀ old t dims a fresh, (allocate t dims).run old = (.ok a, fresh) →
    a = (t, dims.map (fun d => (value d).toNat)) ∧ a.2.prod < 2 ^ 63

def constantArrayResult (value : Z → Int) (t : T) (dims : List Z)
    (allocation : Except Error (T × List Nat) × (I → Option α))
    (element : Except Error α) : Except Error (T × List Nat) × (I → Option α) :=
  match allocation with
  | (.error e, fresh) => (.error e, fresh)
  | (.ok _, fresh) =>
    match element with
    | .error e => (.error e, fresh)
    | .ok x =>
      let shape := dims.map (fun d => (value d).toNat)
      (.ok (t, shape), filledShape fresh shape x)

def ConstantArraySpec : Prop :=
  ∀ (α T Z : Type) (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)),
    TaggedAllocationShapeLaw value allocate →
    ∀ (element : T → Except Error α) (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (t : T) (dims : List Z) (old : I → Option α),
    let typed := fun t dims => constant637 (allocate t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims
    ∀ action ∈ [typed t dims, constantTypedVarargs typed t dims,
      constant642 (allocate t) (stateExceptLift (element t)) (arrayShapeFiller Prod.snd indices) dims,
      constant647 (similar421 (similar420 (allocate t) ())) (stateExceptLift (element t))
        (arrayShapeFiller Prod.snd indices) dims,
      constantDefaultType t typed dims, constantVarargs (constantDefaultType t typed) dims],
      action.run old = constantArrayResult value t dims ((allocate t dims).run old) (element t)

theorem constantArraySpec : ConstantArraySpec := by
  intro α T Z value allocate halloc element indices hindices t dims old typed action hop
  have hcore : (typed t dims).run old =
      constantArrayResult value t dims ((allocate t dims).run old) (element t) := by
    cases ha : (allocate t dims).run old with
    | mk result fresh =>
      cases result with
      | error e =>
        simp only [typed, constant637, stateExcept_bind, ha, constantArrayResult]
      | ok a =>
        obtain ⟨hshape, hn⟩ := halloc old t dims a fresh ha
        cases he : element t with
        | error e =>
          simp only [typed, constant637, stateExcept_bind, stateExceptLift_run,
            ha, he, constantArrayResult]
        | ok x =>
          simp only [typed, constant637, stateExcept_bind, stateExcept_pure,
            stateExceptLift_run, ha, he, constantArrayResult]
          rw [arrayShapeFiller_run Prod.snd indices hindices a hn x fresh]
          simp only [hshape]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcore

def MixedConstantArraySpec : Prop :=
  ∀ (α T Z : Type) (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)),
    TaggedAllocationShapeLaw value allocate →
    ∀ (element : T → Except Error α) (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (t : T) (dims : List (Sum Z Z)) (old : I → Option α),
    let typed := fun t dims => constant637 (allocate t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims
    ∀ action ∈ [constantMixedDims dimensionArgument typed t dims,
      constantTypedVarargs (constantMixedDims dimensionArgument typed) t dims,
      constantDefaultType t (constantMixedDims dimensionArgument typed) dims,
      constantVarargs (constantDefaultType t (constantMixedDims dimensionArgument typed)) dims],
      action.run old =
        constantArrayResult value t (dims.map (fun d => d.elim id id))
          ((allocate t (dims.map (fun d => d.elim id id))).run old) (element t)

theorem mixedConstantArraySpec : MixedConstantArraySpec := by
  intro α T Z value allocate halloc element indices hindices t dims old typed action hop
  have hmap : dims.map dimensionArgument = dims.map (fun d => d.elim id id) := by
    apply List.map_congr_left
    intro d _
    cases d <;> rfl
  have hc := constantArraySpec α T Z value allocate halloc element indices hindices t
    (dims.map (fun d => d.elim id id)) old
    (typed t (dims.map (fun d => d.elim id id))) (by simp [typed])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;>
    simpa only [constantMixedDims, constantTypedVarargs, constantDefaultType, constantVarargs,
      hmap] using hc

def UnsupportedConstantAxesSpec : Prop :=
  ∀ (α T Z : Type)
    (similarAxes : T → List (ConstructorAxis Z) → SlotM α (T × List Nat)),
    (∀ old t dims, (∃ d ∈ dims, unsupportedAxis d) →
      (similarAxes t dims).run old = (.error (.method "similar"), old)) →
    ∀ (element : T → Except Error α) (indices : List Nat → List I)
      (t : T) (dims : List (ConstructorAxis Z)) (old : I → Option α),
    (∃ d ∈ dims, unsupportedAxis d) →
    (constant647 (similarAxes t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims).run old = (.error (.method "similar"), old)

theorem unsupportedConstantAxesSpec : UnsupportedConstantAxesSpec := by
  intro α T Z similarAxes hsimilar element indices t dims old haxis
  simp only [constant647, stateExcept_bind, hsimilar old t dims haxis]

def TaggedCheckedAllocationLaw (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)) : Prop :=
  TaggedAllocationShapeLaw value allocate ∧
  (∀ old t dims, validAllocationDimensions value dims →
    ∃ fresh, (allocate t dims).run old = (.ok (t, dims.map (fun d => (value d).toNat)), fresh)) ∧
  (∀ old t dims, (∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
    (∃ d ∈ dims, value d < 0) →
    ∃ message, (allocate t dims).run old = (.error (.argument message), old)) ∧
  (∀ old t dims, (∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
    (allocate t dims).run old = (.error .inexact, old))

def DocumentedConstantDimensionsSpec : Prop :=
  ∀ (α T Z : Type) (value : Z → Int)
    (allocate : T → List Z → SlotM α (T × List Nat)),
    TaggedCheckedAllocationLaw value allocate →
    ∀ (element : T → Except Error α) (indices : List Nat → List I),
    (∀ dims, dims.prod < 2 ^ 63 → ∀ j,
      j ∈ indices dims ↔ 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int)) →
    ∀ (t : T) (dims : List Z) (old : I → Option α),
    let typed := fun t dims => constant637 (allocate t) (stateExceptLift (element t))
      (arrayShapeFiller Prod.snd indices) dims
    let actions := [typed t dims, constantTypedVarargs typed t dims,
      constant642 (allocate t) (stateExceptLift (element t)) (arrayShapeFiller Prod.snd indices) dims,
      constant647 (similar421 (similar420 (allocate t) ())) (stateExceptLift (element t))
        (arrayShapeFiller Prod.snd indices) dims,
      constantDefaultType t typed dims, constantVarargs (constantDefaultType t typed) dims]
    (∀ x, element t = .ok x → validAllocationDimensions value dims →
      ∃ fresh, ∀ action ∈ actions, action.run old =
        (.ok (t, dims.map (fun d => (value d).toNat)),
          filledShape fresh (dims.map (fun d => (value d).toNat)) x)) ∧
    ((∀ d ∈ dims, IntTy.i64.min ≤ value d ∧ value d ≤ IntTy.i64.max) →
      (∃ d ∈ dims, value d < 0) →
      ∃ message, ∀ action ∈ actions, action.run old = (.error (.argument message), old)) ∧
    ((∃ d ∈ dims, value d < IntTy.i64.min ∨ IntTy.i64.max < value d) →
      ∀ action ∈ actions, action.run old = (.error .inexact, old))

theorem documentedConstantDimensionsSpec : DocumentedConstantDimensionsSpec := by
  intro α T Z value allocate halloc element indices hindices t dims old typed actions
  have hc := constantArraySpec α T Z value allocate halloc.1 element indices hindices t dims old
  refine ⟨?_, ?_, ?_⟩
  · intro x he hvalid
    obtain ⟨fresh, ha⟩ := halloc.2.1 old t dims hvalid
    refine ⟨fresh, ?_⟩
    intro action hop
    have h := hc action hop
    simpa only [constantArrayResult, ha, he] using h
  · intro hrepresentable hnegative
    obtain ⟨message, ha⟩ := halloc.2.2.1 old t dims hrepresentable hnegative
    refine ⟨message, ?_⟩
    intro action hop
    have h := hc action hop
    simpa only [constantArrayResult, ha] using h
  · intro hout action hop
    have ha := halloc.2.2.2 old t dims hout
    have h := hc action hop
    simpa only [constantArrayResult, ha] using h

def CompleteConstantArraySpec : Prop :=
  ConstantArraySpec ∧ MixedConstantArraySpec ∧ UnsupportedConstantAxesSpec ∧
    DocumentedConstantDimensionsSpec

theorem completeConstantArraySpec : CompleteConstantArraySpec :=
  ⟨constantArraySpec, mixedConstantArraySpec, unsupportedConstantAxesSpec,
    documentedConstantDimensionsSpec⟩

@[simp] theorem vector_pure_run (x : β) (heap : VectorHeap α) :
    (pure x : VectorM α β).run heap = .ok (x, heap) := rfl

@[simp] theorem vector_bind_run (action : VectorM α β) (next : β → VectorM α γ)
    (heap : VectorHeap α) :
    (action >>= next).run heap =
      match action.run heap with
      | .error e => .error e
      | .ok (x, state) => (next x).run state := by
  simp only [StateT.run, StateT.bind, Bind.bind, Except.bind]
  cases h : action heap with
  | error e => rfl
  | ok pair => cases pair; rfl

@[simp] theorem vector_throw_run (e : Error) (heap : VectorHeap α) :
    (throw e : VectorM α β).run heap = .error e := rfl

@[simp] theorem vector_lift_run (value : Except Error β) (heap : VectorHeap α) :
    (liftM value : VectorM α β).run heap = value.map (fun x => (x, heap)) := by
  cases value <;> rfl

@[simp] theorem vector_modify_run (f : VectorHeap α → VectorHeap α) (heap : VectorHeap α) :
    (modify f : VectorM α Unit).run heap = .ok ((), f heap) := rfl

@[simp] theorem vector_get_run (heap : VectorHeap α) :
    (get : VectorM α (VectorHeap α)).run heap = .ok (heap, heap) := rfl

@[simp] theorem vector_ite_run (p : Prop) [Decidable p]
    (yes no : VectorM α β) (heap : VectorHeap α) :
    (if p then yes else no).run heap =
      if p then yes.run heap else no.run heap := by
  split <;> rfl

@[simp] theorem heapSlots_run (handle : Nat) (heap : VectorHeap α) :
    (heapSlots handle).run heap =
      match heap[handle]? with
      | none => .error .bounds
      | some slots => .ok (slots, heap) := by
  simp only [heapSlots, vector_bind_run, vector_get_run]
  cases heap[handle]? <;> rfl

@[simp] theorem heapLength_run (handle : Nat) (heap : VectorHeap α) :
    (heapLength handle).run heap =
      match heap[handle]? with
      | none => .error .bounds
      | some slots => .ok (JInt.wrap .i64 slots.length, heap) := by
  simp only [heapLength, vector_bind_run, heapSlots_run]
  cases heap[handle]? <;> rfl

@[simp] theorem heapBounds_run (handle : Nat) (i : I) (heap : VectorHeap α) :
    (heapBounds handle i).run heap =
      match heap[handle]? with
      | none => .error .bounds
      | some slots =>
        if 1 ≤ i.val ∧ i.val ≤ (slots.length : Int) then .ok ((), heap) else .error .bounds := by
  simp only [heapBounds, vector_bind_run, heapSlots_run]
  cases heap[handle]? with
  | none => rfl
  | some slots =>
    by_cases hb : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int) <;>
      simp only [hb, and_self, decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true, vector_pure_run, vector_throw_run]

theorem heapCopyReferences_whole_run (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : Nat) (xs ys : List (Option α))
    (hsrc : heap[src]? = some xs) (hdest : heap[dest]? = some ys)
    (hlen : ys.length = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapCopyReferences convert (dest, one) (src, one) (JInt.wrap .i64 xs.length)).run heap =
      (xs.mapM convert).map (fun values => ((), heap.set dest values)) := by
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
    change wrapInt .i64 (xs.length : Int) = xs.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  have hb : 0 ≤ (xs.length : Int) ∧ 1 ≤ (1 : Int) ∧
      (1 : Int) - 1 + xs.length ≤ ys.length ∧
      1 ≤ (1 : Int) ∧ (1 : Int) - 1 + xs.length ≤ xs.length := by omega
  simp only [heapCopyReferences, vector_bind_run, heapSlots_run,
    hsrc, hdest, hv, hlen, show one.val = 1 from rfl,
    Int.sub_self, Int.zero_add, Int.le_refl, Int.natCast_nonneg, and_self,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    Int.toNat_zero, Int.toNat_natCast, List.drop_zero, List.take_length, vector_lift_run]
  cases hc : xs.mapM convert with
  | error e => simp only [Except.map]
  | ok values =>
    have hdrop : ys.drop xs.length = [] := by rw [← hlen]; exact List.drop_length
    simp only [Except.map, List.take_zero, hdrop,
      List.nil_append, List.append_nil, vector_modify_run]

theorem heapCheckedCopy_zero_eq (convert : Option α → Except Error (Option α))
    (dest src : Nat) (di si n : I) (hn : n.val = 0) :
    heapCheckedCopy convert dest di src si n = pure dest := by
  simp only [heapCheckedCopy, copyto288, copytoImpl, hn, ite_true]

theorem heapCheckedCopy_positive_eq (convert : Option α → Except Error (Option α))
    (dest src : Nat) (di si n : I) (hn : 0 < n.val) :
    heapCheckedCopy convert dest di src si n = (do
      heapBounds dest di
      if !(n.val ≤ ((← heapLength dest) - di + one).val) then throw .bounds
      heapBounds src si
      if !(n.val ≤ ((← heapLength src) - si + one).val) then throw .bounds
      heapCopyReferences convert (dest, di) (src, si) n
      pure dest) := by
  have hn0 : n.val ≠ 0 := by omega
  simp only [heapCheckedCopy, copyto288, copytoImpl, hn0, hn, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false, heapReference, pure_bind]

theorem heapWholeCopy_run (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : Nat) (xs ys : List (Option α))
    (hsrc : heap[src]? = some xs) (hdest : heap[dest]? = some ys)
    (hlen : ys.length = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapWholeCopy convert dest src).run heap =
      if xs = [] then .ok (dest, heap)
      else (xs.mapM convert).map (fun values => (dest, heap.set dest values)) := by
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := by
    change wrapInt .i64 (xs.length : Int) = xs.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  simp only [heapWholeCopy, copyto325, copyto2arg, vector_bind_run,
    vector_pure_run, heapLength_run, hsrc]
  by_cases hz : xs = []
  · simp only [ite_eq_left hz]
    rw [heapCheckedCopy_zero_eq convert dest src one one (JInt.wrap .i64 xs.length)
      (by rw [hv]; simp only [hz, List.length_nil, Int.natCast_zero])]
    exact vector_pure_run _ _
  · have hp : 0 < xs.length := List.length_pos_iff.mpr hz
    have hbi : 1 ≤ (1 : Int) ∧ (1 : Int) ≤ xs.length := by omega
    have hsrem := copy_remaining xs.length 1 hn hbi
    have hn0 : (xs.length : Int) ≠ 0 := by omega
    simp only [ite_eq_right hz]
    rw [heapCheckedCopy_positive_eq convert dest src one one (JInt.wrap .i64 xs.length)
      (by rw [hv]; omega)]
    have hremain : (JInt.wrap .i64 (xs.length : Int) - one + one).val = xs.length := by
      change (JInt.wrap .i64 ((JInt.wrap .i64 (xs.length : Int)).val - one.val) + one).val = _
      rw [show one.val = 1 from rfl]
      simpa only [Int.sub_add_cancel] using hsrem
    simp only [vector_bind_run, vector_pure_run, heapLength_run, heapBounds_run,
      hsrc, hdest, hlen, hv, show one.val = 1 from rfl, hbi, hremain, Int.le_refl,
      and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [heapCopyReferences_whole_run convert heap dest src xs ys hsrc hdest hlen hn]
    cases xs.mapM convert <;> simp only [Except.map]

@[simp] theorem heapAllocate_run (n : Nat) (heap : VectorHeap α) :
    (heapAllocate n).run heap = .ok (heap.length, heap ++ [List.replicate n none]) := rfl

@[simp] theorem heapAllocateArray_run (target : Tag) (dims : List Nat) (heap : VectorHeap α)
    (hd : heapDimensionsFit dims = true) (hn : dims.prod < 2 ^ 63) :
    (heapAllocateArray target dims).run heap =
      .ok (⟨heap.length, target, dims, dims.map (fun n => (1, n))⟩,
        heap ++ [List.replicate dims.prod none]) := by
  simp only [heapAllocateArray, hd, hn, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, vector_bind_run, heapAllocate_run, vector_pure_run]

theorem heapAllocateArray_inexact_run (target : Tag) (dims : List Nat) (heap : VectorHeap α)
    (hd : heapDimensionsFit dims = false) :
    (heapAllocateArray target dims).run heap = .error .inexact := by
  simp only [heapAllocateArray, hd, Bool.not_false, ite_true,
    vector_bind_run, vector_throw_run]

theorem heapAllocateArray_overflow_run (target : Tag) (dims : List Nat) (heap : VectorHeap α)
    (hd : heapDimensionsFit dims = true) (hn : ¬dims.prod < 2 ^ 63) :
    (heapAllocateArray target dims).run heap = .error (.argument "invalid Array dimensions") := by
  simp only [heapAllocateArray, hd, hn, decide_false, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_true, ite_false, vector_bind_run, vector_throw_run]

def heapArrayDimensionError (dims : List Nat) : Error :=
  if heapDimensionsFit dims then .argument "invalid Array dimensions" else .inexact

theorem heapAllocateArray_invalid_run (target : Tag) (dims : List Nat) (heap : VectorHeap α)
    (hd : heapDimensionsFit dims = false ∨ 2 ^ 63 ≤ dims.prod) :
    (heapAllocateArray target dims).run heap = .error (heapArrayDimensionError dims) := by
  cases hf : heapDimensionsFit dims with
  | false =>
    simp only [heapArrayDimensionError, hf, Bool.false_eq_true, ite_false]
    exact heapAllocateArray_inexact_run target dims heap hf
  | true =>
    have hn : ¬dims.prod < 2 ^ 63 := by
      rcases hd with hd | hn
      · simp [hf] at hd
      · omega
    simp only [heapArrayDimensionError, hf, ite_true]
    exact heapAllocateArray_overflow_run target dims heap hf hn

def heapArrayCopy {Tag α : Type} (convert : Option α → Except Error (Option α))
    (dest src : HeapArray Tag) : VectorM α (HeapArray Tag) := do
  let handle ← heapWholeCopy convert dest.handle src.handle
  pure { dest with handle := handle }

def heapArrayAxesCopy {Tag α : Type}
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) :=
  JuliaLean.base.abstractarray.copytoAxesCheck
    (fun a : HeapArray Tag => pure a.axes) (fun a : HeapArray Tag => pure a.axes)
    check (heapArrayCopy convert)

def heapArrayConstructor {Tag α : Type} (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) :=
  arrayConstructor (fun a : HeapArray Tag => pure a.dimensions)
    (heapAllocateArray target) (heapArrayAxesCopy check convert)

def normalizedHeapAxes (axes : List (Int × Nat)) : List (Int × Nat) :=
  axes.map (fun p => (if p.2 = 0 then 1 else p.1, p.2))

def HeapAxesLaw (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (message : String) : Prop :=
  ∀ heap dest src, (check dest src).run heap =
    if normalizedHeapAxes dest = normalizedHeapAxes src then .ok (true, heap)
    else .error (.dimensionMismatch message)

theorem heapArrayCopy_run (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : HeapArray Tag) (xs ys : List (Option α))
    (hsrc : heap[src.handle]? = some xs) (hdest : heap[dest.handle]? = some ys)
    (hlen : ys.length = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapArrayCopy convert dest src).run heap =
      if xs = [] then .ok (dest, heap)
      else (xs.mapM convert).map (fun values => (dest, heap.set dest.handle values)) := by
  simp only [heapArrayCopy, vector_bind_run,
    heapWholeCopy_run convert heap dest.handle src.handle xs ys hsrc hdest hlen hn]
  by_cases hz : xs = []
  · simp only [hz, ite_true, vector_pure_run]
  · simp only [hz, ite_false]
    cases hc : xs.mapM convert <;> rfl

def HeapArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String),
    HeapAxesLaw check message →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    (heapArrayConstructor target check convert src).run heap =
      if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message)

theorem heapArrayConstructorSpec : HeapArrayConstructorSpec := by
  intro Tag α target check convert message hcheck heap src xs hsrc hlen hn hdims
  have hsrcLt : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hsrc).choose
  let fresh : HeapArray Tag :=
    ⟨heap.length, target, src.dimensions, src.dimensions.map (fun n => (1, n))⟩
  let allocated := heap ++ [List.replicate src.dimensions.prod (none : Option α)]
  have hs : allocated[src.handle]? = some xs := by
    simpa only [allocated, List.getElem?_append_left hsrcLt] using hsrc
  have hd : allocated[fresh.handle]? = some (List.replicate src.dimensions.prod none) := by
    simp [allocated, fresh]
  have hc := heapArrayCopy_run convert allocated fresh src xs
    (List.replicate src.dimensions.prod none) hs hd (by simp [hlen]) hn
  simp only [heapArrayConstructor, arrayConstructor, vector_bind_run, vector_pure_run,
    heapAllocateArray_run target src.dimensions heap hdims (by omega)]
  change (heapArrayAxesCopy check convert fresh src).run allocated = _
  simp only [heapArrayAxesCopy, JuliaLean.base.abstractarray.copytoAxesCheck,
    vector_bind_run, vector_pure_run]
  rw [hcheck allocated fresh.axes src.axes]
  by_cases haxes : normalizedHeapAxes fresh.axes = normalizedHeapAxes src.axes
  · dsimp only [fresh] at haxes ⊢
    simp only [haxes, ite_true]
    rw [hc]
    by_cases hz : xs = []
    · simp only [hz, ite_true, List.mapM_nil, Except.map, Pure.pure, Except.pure]
      have hd0 : src.dimensions.prod = 0 := by simp [hlen, hz]
      simp [allocated, hd0, fresh]
    · simp only [hz, ite_false]
      cases hv : xs.mapM convert with
      | error e => rfl
      | ok values =>
        simp [allocated, fresh, List.set_append_right]
  · dsimp only [fresh] at haxes ⊢
    simp only [haxes, ite_false]

def HeapAbstractArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String),
    HeapAxesLaw check message →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    (abstractArrayConstructor
      (fun a => similar419 (heapAllocateArray target) a a.dimensions)
      (heapArrayAxesCopy check convert) src).run heap =
      if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message)

theorem heapAbstractArrayConstructorSpec : HeapAbstractArrayConstructorSpec := by
  intro Tag α target check convert message hcheck heap src xs hs hl hn hdims
  exact heapArrayConstructorSpec Tag α target check convert message hcheck heap src xs hs hl hn hdims

def HeapArrayConvertSpec : Prop :=
  ∀ (Tag α : Type) [DecidableEq Tag] (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (message : String),
    HeapAxesLaw check message →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    let result := (convertArray (fun a => a.elementType == target) id
      (heapArrayConstructor target check convert) src).run heap
    (src.elementType = target → result = .ok (src, heap)) ∧
    (src.elementType ≠ target →
      result = if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
        (xs.mapM convert).map (fun values =>
          (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
            heap ++ [values]))
      else .error (.dimensionMismatch message))

theorem heapArrayConvertSpec : HeapArrayConvertSpec := by
  intro Tag α _ target check convert message hcheck heap src xs hs hl hn hdims result
  refine ⟨?_, ?_⟩
  · intro ht
    simp only [result, convertArray, ht, beq_self_eq_true, ite_true, id_eq, vector_pure_run]
  · intro ht
    simpa only [result, convertArray, show (src.elementType == target) = false by simp [ht],
      Bool.false_eq_true, ite_false] using
      heapArrayConstructorSpec Tag α target check convert message hcheck heap src xs hs hl hn hdims

def HeapCopyFrameSpec : Prop :=
  ∀ (α : Type) (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (dest src : Nat) (xs ys : List (Option α)),
    heap[src]? = some xs → heap[dest]? = some ys →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    (∀ e, xs.mapM convert = .error e → (heapWholeCopy convert dest src).run heap = .error e) ∧
    (∀ values, xs.mapM convert = .ok values →
      ∃ next, (heapWholeCopy convert dest src).run heap = .ok (dest, next) ∧
        next[dest]? = some values ∧ ∀ handle, handle ≠ dest → next[handle]? = heap[handle]?)

theorem heapCopyFrameSpec : HeapCopyFrameSpec := by
  intro α convert heap dest src xs ys hsrc hdest hlen hn
  have hc := heapWholeCopy_run convert heap dest src xs ys hsrc hdest hlen hn
  have hd : dest < heap.length := (List.getElem?_eq_some_iff.mp hdest).choose
  constructor
  · intro e he
    by_cases hz : xs = []
    · simp only [hz, List.mapM_nil, Pure.pure, Except.pure] at he
      cases he
    · simpa only [hz, ite_false, he, Except.map] using hc
  · intro values he
    by_cases hz : xs = []
    · have hv : values = [] := by
        simpa only [hz, List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using he.symm
      have hy : ys = [] := by
        apply List.length_eq_zero_iff.mp
        simpa only [hz, List.length_nil] using hlen
      refine ⟨heap, ?_, ?_, ?_⟩
      · simpa only [hz, ite_true] using hc
      · simpa only [hv, hy] using hdest
      · intro handle _; rfl
    · refine ⟨heap.set dest values, ?_, List.getElem?_set_self hd, ?_⟩
      · simpa only [hz, ite_false, he, Except.map] using hc
      · intro handle hne
        exact List.getElem?_set_ne (Ne.symm hne)

def CompleteCheckedCopySpec : Prop := CheckedCopySpec ∧ HeapCopyFrameSpec

theorem completeCheckedCopySpec : CompleteCheckedCopySpec := ⟨checkedCopySpec, heapCopyFrameSpec⟩

/-- Non-Array implementations use the generic AbstractArray interfaces. -/
structure ForeignHeapArray (Tag : Type) where
  view : HeapArray Tag

def HeapGenericCopyLaw {Tag α : Type}
    (convert : Option α → Except Error (Option α))
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag)) : Prop :=
  ∀ heap dest src xs ys, heap[src.view.handle]? = some xs → heap[dest.handle]? = some ys →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    normalizedHeapAxes dest.axes = normalizedHeapAxes src.view.axes →
    (copy dest src).run heap =
      (xs.mapM convert).map (fun values => (dest, heap.set dest.handle values))

def ForeignHeapArrayConstructorSpec : Prop :=
  ∀ (Tag α : Type) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag))
    (cast : ForeignHeapArray Tag → HeapArray Tag) (message : String),
    HeapAxesLaw check message → HeapGenericCopyLaw convert copy →
    ∀ (heap : VectorHeap α) (src : ForeignHeapArray Tag) (xs : List (Option α)),
    heap[src.view.handle]? = some xs → src.view.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.view.dimensions = true →
    let constructor := arrayConstructor (fun s : ForeignHeapArray Tag => pure s.view.dimensions)
      (heapAllocateArray target) (JuliaLean.base.abstractarray.copytoAxesCheck
        (fun a : HeapArray Tag => pure a.axes) (fun s : ForeignHeapArray Tag => pure s.view.axes) check copy)
    ∀ operation ∈ [constructor, convertArray (fun _ => false) cast constructor],
      (operation src).run heap =
        if normalizedHeapAxes (src.view.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.view.axes then
          (xs.mapM convert).map (fun values =>
            (HeapArray.mk heap.length target src.view.dimensions
              (src.view.dimensions.map (fun n => (1, n))), heap ++ [values]))
        else .error (.dimensionMismatch message)

theorem foreignHeapArrayConstructorSpec : ForeignHeapArrayConstructorSpec := by
  intro Tag α target check convert copy cast message hcheck hcopy heap src xs hs hl hn hdims ctor operation hop
  have hsl : src.view.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  let fresh : HeapArray Tag :=
    ⟨heap.length, target, src.view.dimensions, src.view.dimensions.map (fun n => (1, n))⟩
  let allocated := heap ++ [List.replicate src.view.dimensions.prod (none : Option α)]
  have hsrc : allocated[src.view.handle]? = some xs := by
    simpa only [allocated, List.getElem?_append_left hsl] using hs
  have hdest : allocated[fresh.handle]? = some (List.replicate src.view.dimensions.prod none) := by
    simp [allocated, fresh]
  have core : (ctor src).run heap =
      if normalizedHeapAxes fresh.axes = normalizedHeapAxes src.view.axes then
        (xs.mapM convert).map (fun values => (fresh, heap ++ [values]))
      else .error (.dimensionMismatch message) := by
    simp only [ctor, arrayConstructor, JuliaLean.base.abstractarray.copytoAxesCheck,
      vector_bind_run, vector_pure_run,
      heapAllocateArray_run target src.view.dimensions heap hdims (by omega)]
    rw [hcheck allocated fresh.axes src.view.axes]
    by_cases hax : normalizedHeapAxes fresh.axes = normalizedHeapAxes src.view.axes
    · simp only [hax, ite_true]
      rw [hcopy allocated fresh src xs (List.replicate src.view.dimensions.prod none)
        hsrc hdest (by simp [hl]) hn hax]
      cases hc : xs.mapM convert <;> simp [allocated, fresh, List.set_append_right]
    · simp only [hax, ite_false]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact core
  · simpa only [convertArray, Bool.false_eq_true, ite_false] using core

def ForeignHeapAbstractConstructorSpec : Prop :=
  ∀ (Tag α : Type) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag))
    (similar : ForeignHeapArray Tag → VectorM α (HeapArray Tag)) (message : String),
    HeapAxesLaw check message → HeapGenericCopyLaw convert copy →
    (∀ heap src dest next, (similar src).run heap = .ok (dest, next) →
      dest.handle = heap.length ∧ dest.elementType = target ∧
      dest.dimensions = src.view.dimensions ∧
      next = heap ++ [List.replicate src.view.dimensions.prod none]) →
    ∀ (heap : VectorHeap α) (src : ForeignHeapArray Tag) (xs : List (Option α)),
    heap[src.view.handle]? = some xs → src.view.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    (abstractArrayConstructor similar (JuliaLean.base.abstractarray.copytoAxesCheck
      (fun a : HeapArray Tag => pure a.axes) (fun s : ForeignHeapArray Tag => pure s.view.axes) check copy)
      src).run heap =
      match (similar src).run heap with
      | .error e => .error e
      | .ok (dest, _) =>
        if normalizedHeapAxes dest.axes = normalizedHeapAxes src.view.axes then
          (xs.mapM convert).map (fun values => (dest, heap ++ [values]))
        else .error (.dimensionMismatch message)

theorem foreignHeapAbstractConstructorSpec : ForeignHeapAbstractConstructorSpec := by
  intro Tag α target check convert copy similar message hcheck hcopy hsimilar heap src xs hs hl hn
  have hsl : src.view.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  simp only [abstractArrayConstructor, vector_bind_run]
  cases ha : (similar src).run heap with
  | error e => rfl
  | ok pair =>
    obtain ⟨dest, next⟩ := pair
    obtain ⟨hd, ht, hdim, hnext⟩ := hsimilar heap src dest next ha
    have hsrc : next[src.view.handle]? = some xs := by
      simpa only [hnext, List.getElem?_append_left hsl] using hs
    have hdest : next[dest.handle]? = some (List.replicate src.view.dimensions.prod none) := by
      simp [hnext, hd]
    simp only [JuliaLean.base.abstractarray.copytoAxesCheck, vector_bind_run, vector_pure_run]
    rw [hcheck next dest.axes src.view.axes]
    by_cases hax : normalizedHeapAxes dest.axes = normalizedHeapAxes src.view.axes
    · simp only [hax, ite_true]
      rw [hcopy next dest src xs (List.replicate src.view.dimensions.prod none)
        hsrc hdest (by simp [hl]) hn hax]
      cases hc : xs.mapM convert <;> simp [hnext, hd, List.set_append_right]
    · simp only [hax, ite_false]

def HeapNativeDimensionErrorsSpec : Prop :=
  ∀ (Tag α : Type) [DecidableEq Tag] (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α)) (heap : VectorHeap α) (src : HeapArray Tag),
    (heapDimensionsFit src.dimensions = false ∨ 2 ^ 63 ≤ src.dimensions.prod) →
    ((heapArrayConstructor target check convert src).run heap =
      .error (heapArrayDimensionError src.dimensions)) ∧
    ((abstractArrayConstructor
      (fun a => similar419 (heapAllocateArray target) a a.dimensions)
      (heapArrayAxesCopy check convert) src).run heap =
      .error (heapArrayDimensionError src.dimensions)) ∧
    ((convertArray (fun a => a.elementType == target) id
      (heapArrayConstructor target check convert) src).run heap =
      if src.elementType = target then .ok (src, heap)
      else .error (heapArrayDimensionError src.dimensions))

theorem heapNativeDimensionErrorsSpec : HeapNativeDimensionErrorsSpec := by
  intro Tag α _ target check convert heap src hd
  have ha := heapAllocateArray_invalid_run target src.dimensions heap hd
  have hc : (heapArrayConstructor target check convert src).run heap =
      .error (heapArrayDimensionError src.dimensions) := by
    simp only [heapArrayConstructor, arrayConstructor, vector_bind_run, vector_pure_run, ha]
  refine ⟨hc, ?_, ?_⟩
  · simp only [abstractArrayConstructor, similar419, vector_bind_run, ha]
  · by_cases ht : src.elementType = target
    · simp only [convertArray, ht, beq_self_eq_true, ite_true, id_eq, vector_pure_run]
    · simp only [convertArray, show (src.elementType == target) = false by simp [ht],
        Bool.false_eq_true, ite_false, hc, ite_eq_right ht]

def HeapForeignDimensionErrorsSpec : Prop :=
  ∀ (Tag α : Type) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (copy : HeapArray Tag → ForeignHeapArray Tag → VectorM α (HeapArray Tag))
    (cast : ForeignHeapArray Tag → HeapArray Tag)
    (heap : VectorHeap α) (src : ForeignHeapArray Tag),
    (heapDimensionsFit src.view.dimensions = false ∨ 2 ^ 63 ≤ src.view.dimensions.prod) →
    let constructor := arrayConstructor (fun s : ForeignHeapArray Tag => pure s.view.dimensions)
      (heapAllocateArray target) (JuliaLean.base.abstractarray.copytoAxesCheck
        (fun a : HeapArray Tag => pure a.axes) (fun s : ForeignHeapArray Tag => pure s.view.axes) check copy)
    ∀ operation ∈ [constructor, convertArray (fun _ => false) cast constructor],
      (operation src).run heap = .error (heapArrayDimensionError src.view.dimensions)

theorem heapForeignDimensionErrorsSpec : HeapForeignDimensionErrorsSpec := by
  intro Tag α target check copy cast heap src hd ctor operation hop
  have ha := heapAllocateArray_invalid_run target src.view.dimensions heap hd
  have hc : (ctor src).run heap = .error (heapArrayDimensionError src.view.dimensions) := by
    simp only [ctor, arrayConstructor, vector_bind_run, vector_pure_run, ha]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact hc
  · simpa only [convertArray, Bool.false_eq_true, ite_false] using hc

/-- Source and destination allocations retain separate, typed element views. -/
theorem typed_slot_mapM (convert : β → Except Error α)
    (slotConvert : Option (Sum α β) → Except Error (Option (Sum α β)))
    (hlaw : ∀ x, slotConvert (some (.inr x)) = (convert x).map (fun y => some (.inl y)))
    (xs : List β) :
    (xs.map (fun x => some (Sum.inr x))).mapM slotConvert =
      (xs.mapM convert).map (fun values => values.map (fun y => some (Sum.inl y))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, hlaw, Bind.bind, Except.bind]
    cases hx : convert x with
    | error e => simp only [Except.map]
    | ok y =>
      simp only [Except.map]
      rw [ih]
      cases xs.mapM convert <;> rfl

def TypedHeapConstructionSpec : Prop :=
  ∀ (Tag α β : Type) [DecidableEq Tag] (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM (Sum α β) Bool)
    (convert : β → Except Error α)
    (slotConvert : Option (Sum α β) → Except Error (Option (Sum α β)))
    (message : String),
    HeapAxesLaw check message →
    (∀ x, slotConvert (some (.inr x)) = (convert x).map (fun y => some (.inl y))) →
    ∀ (heap : VectorHeap (Sum α β)) (src : HeapArray Tag) (xs : List β),
    heap[src.handle]? = some (xs.map (fun x => some (.inr x))) →
    src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    let expected := if normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes then
      (xs.mapM convert).map (fun values =>
        (HeapArray.mk heap.length target src.dimensions (src.dimensions.map (fun n => (1, n))),
          heap ++ [values.map (fun y => some (.inl y))]))
      else .error (.dimensionMismatch message)
    (∀ operation ∈ [heapArrayConstructor target check slotConvert,
      abstractArrayConstructor
        (fun a => similar419 (heapAllocateArray target) a a.dimensions)
        (heapArrayAxesCopy check slotConvert)],
      (operation src).run heap = expected) ∧
    (src.elementType ≠ target →
      (convertArray (fun a => a.elementType == target) id
        (heapArrayConstructor target check slotConvert) src).run heap = expected)

theorem typedHeapConstructionSpec : TypedHeapConstructionSpec := by
  intro Tag α β _ target check convert slotConvert message hcheck hslot heap src xs hs hl hn hdims expected
  have hc := heapArrayConstructorSpec Tag (Sum α β) target check slotConvert message hcheck heap src
    (xs.map (fun x => some (.inr x))) hs (by simpa using hl) (by simpa using hn) hdims
  have he : (heapArrayConstructor target check slotConvert src).run heap = expected := by
    rw [typed_slot_mapM convert slotConvert hslot xs] at hc
    cases hv : xs.mapM convert <;> simpa only [expected, hv, Except.map] using hc
  constructor
  · intro operation hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> exact he
  · intro hne
    simpa only [convertArray, show (src.elementType == target) = false by simp [hne],
      Bool.false_eq_true, ite_false] using he

theorem bitinteger_array_conversion (T : IntTy) (x : JInt S) :
    (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact) =
      if T.min ≤ x.val ∧ x.val ≤ T.max
      then .ok (JInt.wrap T x.val) else .error .inexact := by
  by_cases h : T.min ≤ x.val ∧ x.val ≤ T.max
  · simp only [JuliaLean.base.int.convert, JInt.convert, h, and_self, ite_true, dite_true, Except.mapError,
      Except.ok.injEq]
    apply Subtype.ext
    change x.val = wrapInt T x.val
    exact (wrapInt_of_inRange T x.val h).symm
  · simp [JuliaLean.base.int.convert, JInt.convert, h, Except.mapError]

theorem bitinteger_array_mapM_success (T : IntTy) (xs : List (JInt S))
    (hfit : ∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max) :
    (xs.mapM (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))) =
      .ok (xs.map (fun x => JInt.wrap T x.val)) := by
  apply mapM_ok_of_mem
  intro x hx
  rw [bitinteger_array_conversion, ite_eq_left (hfit x hx)]

theorem bitinteger_array_mapM_failure (T : IntTy) (xs : List (JInt S))
    (hbad : ∃ x ∈ xs, ¬(T.min ≤ x.val ∧ x.val ≤ T.max)) :
    (xs.mapM (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))) =
      .error .inexact := by
  induction xs with
  | nil => simp at hbad
  | cons x xs ih =>
    simp only [List.mapM_cons]
    rw [bitinteger_array_conversion]
    by_cases hx : T.min ≤ x.val ∧ x.val ≤ T.max
    · simp only [hx, and_self, ite_true, Bind.bind, Except.bind]
      have htail : ∃ y ∈ xs, ¬(T.min ≤ y.val ∧ y.val ≤ T.max) := by
        obtain ⟨y, hy, hb⟩ := hbad
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hb hx)
        · exact ⟨y, hy, hb⟩
      rw [ih htail]
    · simp only [hx, ite_false, Bind.bind, Except.bind]

def BitIntegerHeapConstructionSpec : Prop :=
  ∀ (T S : IntTy)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM (Sum (JInt T) (JInt S)) Bool)
    (slotConvert : Option (Sum (JInt T) (JInt S)) → Except Error (Option (Sum (JInt T) (JInt S))))
    (message : String),
    HeapAxesLaw check message →
    (∀ x, slotConvert (some (.inr x)) =
      ((JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)).map (fun y => some (.inl y))) →
    ∀ (heap : VectorHeap (Sum (JInt T) (JInt S))) (src : HeapArray IntTy) (xs : List (JInt S)),
    heap[src.handle]? = some (xs.map (fun x => some (.inr x))) →
    src.elementType = S → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    normalizedHeapAxes (src.dimensions.map (fun n => (1, n))) = normalizedHeapAxes src.axes →
    let operations := [heapArrayConstructor T check slotConvert,
      abstractArrayConstructor (fun a => similar419 (heapAllocateArray T) a a.dimensions)
        (heapArrayAxesCopy check slotConvert)]
    (∀ operation ∈ operations,
      (∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max) →
      (operation src).run heap =
        .ok (⟨heap.length, T, src.dimensions, src.dimensions.map (fun n => (1, n))⟩,
          heap ++ [xs.map (fun x => some (.inl (JInt.wrap T x.val)))])) ∧
    (∀ operation ∈ operations,
      (∃ x ∈ xs, ¬(T.min ≤ x.val ∧ x.val ≤ T.max)) →
      (operation src).run heap = .error .inexact)

theorem bitIntegerHeapConstructionSpec : BitIntegerHeapConstructionSpec := by
  intro T S check slotConvert message hcheck hslot heap src xs hs htype hl hn hdims haxes operations
  have hc := (typedHeapConstructionSpec IntTy (JInt T) (JInt S) T check
    (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))
    slotConvert message hcheck hslot heap src xs hs hl hn hdims).1
  constructor
  · intro operation hop hfit
    have h := hc operation hop
    simpa only [haxes, ite_true, bitinteger_array_mapM_success T xs hfit, Except.map,
      List.map_map, Function.comp_def] using h
  · intro operation hop hbad
    have h := hc operation hop
    simpa only [haxes, ite_true, bitinteger_array_mapM_failure T xs hbad, Except.map] using h

def CompleteHeapArrayConstructorSpec : Prop :=
  HeapArrayConstructorSpec ∧ ForeignHeapArrayConstructorSpec ∧
    HeapNativeDimensionErrorsSpec ∧ HeapForeignDimensionErrorsSpec ∧
    TypedHeapConstructionSpec ∧ BitIntegerHeapConstructionSpec
theorem completeHeapArrayConstructorSpec : CompleteHeapArrayConstructorSpec :=
  ⟨heapArrayConstructorSpec, foreignHeapArrayConstructorSpec,
    heapNativeDimensionErrorsSpec, heapForeignDimensionErrorsSpec,
    typedHeapConstructionSpec, bitIntegerHeapConstructionSpec⟩

def CompleteHeapArrayConvertSpec : Prop :=
  HeapArrayConvertSpec ∧ ForeignHeapArrayConstructorSpec ∧
    HeapNativeDimensionErrorsSpec ∧ HeapForeignDimensionErrorsSpec ∧
    TypedHeapConstructionSpec ∧ BitIntegerHeapConstructionSpec
theorem completeHeapArrayConvertSpec : CompleteHeapArrayConvertSpec :=
  ⟨heapArrayConvertSpec, foreignHeapArrayConstructorSpec,
    heapNativeDimensionErrorsSpec, heapForeignDimensionErrorsSpec,
    typedHeapConstructionSpec, bitIntegerHeapConstructionSpec⟩

def CompleteHeapAbstractConstructorSpec : Prop :=
  HeapAbstractArrayConstructorSpec ∧ ForeignHeapAbstractConstructorSpec ∧
    HeapNativeDimensionErrorsSpec ∧ TypedHeapConstructionSpec ∧ BitIntegerHeapConstructionSpec
theorem completeHeapAbstractConstructorSpec : CompleteHeapAbstractConstructorSpec :=
  ⟨heapAbstractArrayConstructorSpec, foreignHeapAbstractConstructorSpec,
    heapNativeDimensionErrorsSpec, typedHeapConstructionSpec, bitIntegerHeapConstructionSpec⟩

@[simp] theorem mutation_get_run (s : MutableMemory α) :
    (get : MutationM α (MutableMemory α)).run s = (.ok s, s) := rfl

@[simp] theorem mutation_modify_run (f : MutableMemory α → MutableMemory α)
    (s : MutableMemory α) :
    (modify f : MutationM α Unit).run s = (.ok (), f s) := rfl

theorem mutableOverallocation_run (n : I) :
    ∃ capacity : I, ∀ s : MutableMemory α,
      (mutableStorage.overallocation n).run s = (.ok capacity, s) := by
  simp only [mutableStorage, overallocation, stateExcept_bind, stateExcept_pure]
  exact ⟨_, fun _ => rfl⟩

@[simp] theorem mutableVector_run (s : MutableMemory α) (handle : Nat) :
    (mutableVector handle).run s =
      match s.arrays[handle]? with
      | none => (.error .bounds, s)
      | some a => (.ok a, s) := by
  simp only [mutableVector, stateExcept_bind, mutation_get_run]
  cases s.arrays[handle]? <;> rfl

theorem mutableLength_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) :
    (mutableLength handle).run s = (.ok a.size, s) := by
  simp only [mutableLength, stateExcept_bind, mutableVector_run, ha, stateExcept_pure]

theorem mutableRef_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) :
    (mutableRef handle).run s = (.ok a.reference, s) := by
  simp only [mutableRef, stateExcept_bind, mutableVector_run, ha, stateExcept_pure]

theorem memoryRead_run (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) :
    (memoryRead mem).run s = (.ok slots, s) := by
  simp only [memoryRead, stateExcept_bind, mutation_get_run, hm, stateExcept_pure]

theorem memoryWrite_run (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ (slots.length : Int)) (x : Option α) :
    (memoryWrite mem i x).run s =
      (.ok (), {s with memories := s.memories.set mem (slots.set (i.val - 1).toNat x)}) := by
  simp only [memoryWrite, stateExcept_bind, memoryRead_run s mem slots hm, hi,
    and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    mutation_modify_run]

theorem mutableMemLength_run (s : MutableMemory α) (mem : Nat) (slots : List (Option α))
    (hm : s.memories[mem]? = some slots) :
    (mutableStorage.memLength mem).run s = (.ok (JInt.wrap .i64 slots.length), s) := by
  change (do
    let xs ← memoryRead mem
    pure (JInt.wrap .i64 (xs.length : Int)) : MutationM α I).run s = _
  simp only [stateExcept_bind, memoryRead_run s mem slots hm, stateExcept_pure]

theorem mutableCheckedAdd_run (s : MutableMemory α) (x y : I)
    (h : IntTy.i64.min ≤ x.val + y.val ∧ x.val + y.val ≤ IntTy.i64.max) :
    (mutableStorage.checkedAdd x y).run s = (.ok (x + y), s) := by
  change (if _ then (pure (x + y) : MutationM α I) else throw Error.overflow).run s = _
  simp only [h, and_self, ite_true, stateExcept_pure]

theorem mutableDivideFour_run (s : MutableMemory α) (x : I) :
    (mutableStorage.divide x (JInt.wrap .i64 4)).run s =
      (.ok (JInt.wrap .i64 (x.val.tdiv 4)), s) := rfl

theorem mutableMemoryAllocate_run (s : MutableMemory α) (mem : Nat) (n : I)
    (hn : ¬ n < zero) :
    (mutableStorage.allocate mem n).run s =
      (.ok s.memories.length, {s with memories := s.memories ++ [List.replicate n.val.toNat none]}) := by
  change (if n < zero then _ else _ : MutationM α Nat).run s = _
  simp only [hn, ite_false, stateExcept_bind, mutation_get_run,
    mutation_modify_run, stateExcept_pure]

theorem mutableSet_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) (slots : List (Option α))
    (hm : s.memories[a.reference.1]? = some slots) (i : I) (x : α)
    (hb : one ≤ i ∧ i ≤ a.size)
    (hr : 1 ≤ (a.reference.2 + i - one).val ∧
      (a.reference.2 + i - one).val ≤ (slots.length : Int)) :
    (mutableSet handle x i).run s =
      (.ok (), {s with memories := (s.memories.set a.reference.1
        (slots.set ((a.reference.2 + i - one).val - 1).toNat (some x)))}) := by
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds, stateExcept_bind,
    mutableLength_run s handle a ha, stateExcept_pure, hb, and_self, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false, mutableMemoryref,
    mutableRef_run s handle a ha, memoryWrite_run s a.reference.1 slots hm _ hr]

theorem memoryWrites_prefix_run (values : List (Option α)) (s : MutableMemory α)
    (mem : Nat) (written suffix : List (Option α))
    (hm : s.memories[mem]? = some (written ++ suffix))
    (hfit : values.length ≤ suffix.length)
    (hcapacity : written.length + suffix.length < 2 ^ 63) :
    (forIn (values.zipIdx written.length) () (fun (pair : Option α × Nat) _ => do
      memoryWrite mem (one + JInt.wrap .i64 pair.2) pair.1
      pure (ForInStep.yield ()))).run s =
      (.ok (), {s with memories := s.memories.set mem (written ++ values ++ suffix.drop values.length)}) := by
  induction values generalizing s written suffix with
  | nil =>
    have hself : s.memories.set mem (written ++ suffix) = s.memories := by
      obtain ⟨h, hv⟩ := List.getElem?_eq_some_iff.mp hm
      rw [← hv]
      exact List.set_getElem_self h
    simp only [List.zipIdx_nil, List.forIn_nil, stateExcept_pure,
      List.append_nil, List.length_nil, List.drop_zero, hself]
  | cons x xs ih =>
    cases suffix with
    | nil => simp only [List.length_nil, List.length_cons] at hfit; omega
    | cons y ys =>
      have hp : written.length < 2 ^ 63 := by simp only [List.length_cons] at hcapacity; omega
      have hk : wrapInt .i64 (written.length : Int) = written.length := by
        apply wrapInt_of_inRange
        simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
        omega
      have haddr : (one + JInt.wrap .i64 (written.length : Int)).val = written.length + 1 := by
        change wrapInt .i64 (1 + wrapInt .i64 (written.length : Int)) = _
        rw [hk]
        have hh : wrapInt .i64 (1 + (written.length : Int)) = 1 + written.length := by
          apply wrapInt_of_inRange
          simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
          simp only [List.length_cons] at hcapacity
          omega
        rw [hh]
        omega
      have hb : 1 ≤ (one + JInt.wrap .i64 (written.length : Int)).val ∧
          (one + JInt.wrap .i64 (written.length : Int)).val ≤
            ((written ++ y :: ys).length : Int) := by
        rw [haddr]
        simp only [List.length_append, List.length_cons]
        omega
      have hset : (written ++ y :: ys).set
          ((one + JInt.wrap .i64 (written.length : Int)).val - 1).toNat x =
          (written ++ [x]) ++ ys := by
        rw [haddr]
        simp
      let mid : MutableMemory α :=
        {s with memories := s.memories.set mem ((written ++ [x]) ++ ys)}
      have hmLt := (List.getElem?_eq_some_iff.mp hm).choose
      have hmid : mid.memories[mem]? = some ((written ++ [x]) ++ ys) :=
        List.getElem?_set_self hmLt
      have hrest := ih mid (written ++ [x]) ys hmid (by simpa using hfit)
        (by simp only [List.length_append, List.length_cons,
          List.length_nil] at *; omega)
      simp only [List.zipIdx_cons, List.forIn_cons, stateExcept_bind,
        memoryWrite_run s mem (written ++ y :: ys) hm _ hb, hset, stateExcept_pure]
      have hindex : written.length + 1 = (written ++ [x]).length := by simp
      rw [hindex]
      change (forIn (xs.zipIdx (written ++ [x]).length) ()
        (fun (pair : Option α × Nat) _ => do
          memoryWrite mem (one + JInt.wrap .i64 pair.2) pair.1
          pure (ForInStep.yield ())) : MutationM α Unit).run mid = _
      rw [hrest]
      simp [mid, List.append_assoc]

theorem memoryMove_prefix_run (s : MutableMemory α) (dest src : Nat)
    (destination source : List (Option α))
    (hd : s.memories[dest]? = some destination) (hs : s.memories[src]? = some source)
    (n : I) (hn : 0 ≤ n.val)
    (hnd : n.val ≤ (destination.length : Int)) (hns : n.val ≤ (source.length : Int))
    (hcap : destination.length < 2 ^ 63) :
    (memoryMove dest one src one n).run s =
      (.ok (), {s with memories := (s.memories.set dest
        (source.take n.val.toNat ++ destination.drop n.val.toNat))}) := by
  have htake : (source.take n.val.toNat).length = n.val.toNat := by
    rw [List.length_take]
    omega
  have hw := memoryWrites_prefix_run (source.take n.val.toNat) s dest [] destination
    (by simpa using hd) (by rw [htake]; omega) (by simpa using hcap)
  simp only [List.length_nil, List.nil_append, htake] at hw
  simp only [memoryMove, stateExcept_bind, memoryRead_run s src source hs,
    memoryRead_run s dest destination hd, show one.val = 1 from rfl, Int.sub_self,
    Int.zero_add, hn, hnd, hns, Int.le_refl, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, Int.toNat_zero, List.drop_zero]
  simp only [hw, stateExcept_pure]

@[simp] theorem jint_i64_sub_zero (x : I) : x - zero = x := by
  apply Subtype.ext
  change wrapInt .i64 (x.val - 0) = x.val
  rw [Int.sub_zero]
  exact wrapInt_of_inRange .i64 x.val x.property

@[simp] theorem jint_i64_zero_add (x : I) : zero + x = x := by
  apply Subtype.ext
  change wrapInt .i64 (0 + x.val) = x.val
  rw [Int.zero_add]
  exact wrapInt_of_inRange .i64 x.val x.property

theorem growendInternal_relocation_tail (s : MutableMemory α) (handle mem : Nat)
    (n : I) (source : List (Option α))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some source)
    (hnfit : IntTy.i64.min ≤ n.val + one.val ∧ n.val + one.val ≤ IntTy.i64.max)
    (hvalid : ¬ (one < one || zero > JInt.wrap .i64 (source.length : Int) ||
      n > JInt.wrap .i64 (source.length : Int)))
    (hzfit : IntTy.i64.min ≤ zero.val + (n + one).val ∧
      zero.val + (n + one).val ≤ IntTy.i64.max)
    (hslide : ¬ zero > n + one) :
    (growendInternal mutableStorage handle one n).run s =
      (do
        let suggested ← mutableStorage.overallocation (JInt.wrap .i64 (source.length : Int))
        let fresh ← mutableStorage.allocate mem (max suggested (n + one))
        let newref ← mutableStorage.memoryref fresh one
        mutableStorage.copyRef newref (mem, one) n
        let _ ←
          if (mutableStorage (α := α)).sameMem fresh mem then do
            for j in intRange (max one (one + n)) (one + n - one) do
              mutableStorage.unsetMemory mem j
          else pure ()
        if !((mutableStorage (α := α)).sameRef (mem, one) (← mutableStorage.ref handle)) then
          throw (.concurrency "Vector can not be resized concurrently")
        else mutableStorage.setRef handle newref : MutationM α Unit).run s := by
  have hml := mutableMemLength_run s mem source hm
  have hca := mutableCheckedAdd_run s n one hnfit
  have hcz := mutableCheckedAdd_run s zero (n + one) hzfit
  have hdiv := mutableDivideFour_run s (n + one)
  simp only [mutableStorage] at hml hca hcz hdiv
  rw [growendInternal]
  dsimp only [mutableStorage]
  rw [stateExcept_bind, mutableRef_run s handle ⟨(mem, one), n⟩ ha]
  dsimp only
  rw [stateExcept_bind, hml]
  dsimp only
  rw [stateExcept_bind, hca]
  dsimp only
  simp only [show one - one = zero from rfl, jint_i64_sub_zero, hvalid, Bool.false_eq_true, ite_false]
  rw [stateExcept_bind, hcz]
  dsimp only
  simp only [jint_i64_zero_add]
  rw [stateExcept_bind, hdiv]
  dsimp only
  simp only [hslide, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
  rfl

def relocatedVectorMemory (s : MutableMemory α) (handle : Nat)
    (n capacity : I) (source : List (Option α)) : MutableMemory α := {
  memories := (s.memories ++ [List.replicate capacity.val.toNat none]).set s.memories.length
    (source.take n.val.toNat ++ (List.replicate capacity.val.toNat none).drop n.val.toNat)
  arrays := s.arrays.set handle ⟨(s.memories.length, one), n⟩}

theorem relocationStorageTail_run (s : MutableMemory α)
    (handle mem : Nat) (n : I) (source : List (Option α))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some source)
    (hn : 0 ≤ n.val) (hsource : n.val ≤ (source.length : Int))
    (hnew : n.val + 1 ≤ IntTy.i64.max)
    (suggested : I)
    (hover : ∀ state : MutableMemory α,
      (mutableStorage.overallocation (JInt.wrap .i64 (source.length : Int))).run state =
        (.ok suggested, state)) :
    (do
      let proposed ← mutableStorage.overallocation (JInt.wrap .i64 (source.length : Int))
      let fresh ← mutableStorage.allocate mem (max proposed (n + one))
      let newref ← mutableStorage.memoryref fresh one
      mutableStorage.copyRef newref (mem, one) n
      let _ ←
        if (mutableStorage (α := α)).sameMem fresh mem then do
          for j in intRange (max one (one + n)) (one + n - one) do
            mutableStorage.unsetMemory mem j
        else pure ()
      if !((mutableStorage (α := α)).sameRef (mem, one) (← mutableStorage.ref handle)) then
        throw (.concurrency "Vector can not be resized concurrently")
      else mutableStorage.setRef handle newref : MutationM α Unit).run s =
      (.ok (), relocatedVectorMemory s handle n (max suggested (n + one)) source) := by
  let newlen := n + one
  let capacity := max suggested newlen
  have hnv : newlen.val = n.val + 1 := by
    change wrapInt .i64 (n.val + 1) = n.val + 1
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.signed, IntTy.bits]
    exact ⟨by omega, hnew⟩
  have hcapge : newlen ≤ capacity := by
    change newlen.val ≤ max suggested.val newlen.val
    exact Int.le_max_right _ _
  have hcapnonneg : ¬ capacity < zero := by
    change ¬ capacity.val < (0 : Int)
    change newlen.val ≤ capacity.val at hcapge
    omega
  have hcap : capacity.val.toNat < 2 ^ 63 := by
    have hb := capacity.property.2
    change capacity.val ≤ 9223372036854775807 at hb
    change capacity.val.toNat < 9223372036854775808
    omega
  let allocated : MutableMemory α :=
    {s with memories := s.memories ++ [List.replicate capacity.val.toNat none]}
  have hmLt := (List.getElem?_eq_some_iff.mp hm).choose
  have hs : allocated.memories[mem]? = some source := by
    simpa only [allocated, List.getElem?_append_left hmLt] using hm
  have hd : allocated.memories[s.memories.length]? =
      some (List.replicate capacity.val.toNat none) := by simp [allocated]
  have hcopy := memoryMove_prefix_run allocated s.memories.length mem
    (List.replicate capacity.val.toNat none) source hd hs n hn
    (by simp only [List.length_replicate]; change newlen.val ≤ capacity.val at hcapge; omega)
    hsource (by simpa using hcap)
  dsimp only [capacity, newlen] at hcapnonneg
  have ho := hover s
  have hallocate := mutableMemoryAllocate_run s mem (max suggested (n + one)) hcapnonneg
  simp only [mutableStorage] at ho hallocate
  dsimp only [mutableStorage]
  rw [stateExcept_bind, ho]
  dsimp only
  rw [stateExcept_bind, hallocate]
  dsimp only
  simp only [stateExcept_bind, stateExcept_pure]
  rw [hcopy]
  let moved : MutableMemory α := {allocated with memories :=
    (allocated.memories.set s.memories.length
      (source.take n.val.toNat ++ (List.replicate capacity.val.toNat none).drop n.val.toNat))}
  have ham : moved.arrays[handle]? = some ⟨(mem, one), n⟩ := ha
  have hne : s.memories.length ≠ mem := by omega
  dsimp only
  simp only [show (s.memories.length == mem) = false by simp [hne],
    Bool.false_eq_true, ite_false, stateExcept_bind]
  rw [mutableRef_run moved handle ⟨(mem, one), n⟩ ham]
  dsimp only
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false, stateExcept_bind]
  rw [mutableVector_run]
  simp only [ham, mutation_modify_run]
  rfl

theorem collectorLengthFits (capacity : Nat) (hcap : capacity < 2 ^ 63) :
    (JInt.wrap .i64 (capacity : Int)).val = capacity := by
  change wrapInt .i64 (capacity : Int) = capacity
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (capacity : Int) ∧
    (capacity : Int) ≤ 9223372036854775807
  change capacity < 9223372036854775808 at hcap
  omega

theorem collectorIncrementFits (n : I) (hn : 0 ≤ n.val)
    (hnew : n.val + 1 ≤ IntTy.i64.max) :
    IntTy.i64.min ≤ n.val + one.val ∧ n.val + one.val ≤ IntTy.i64.max := by
  change IntTy.i64.min ≤ n.val + 1 ∧ n.val + 1 ≤ IntTy.i64.max
  exact ⟨by change -9223372036854775808 ≤ n.val + 1; omega, hnew⟩

theorem collectorZeroAddFits (n : I) :
    IntTy.i64.min ≤ zero.val + n.val ∧ zero.val + n.val ≤ IntTy.i64.max := by
  change IntTy.i64.min ≤ 0 + n.val ∧ 0 + n.val ≤ IntTy.i64.max
  simpa only [Int.zero_add] using n.property

theorem noThreeChecks (p q r : Prop) [Decidable p] [Decidable q] [Decidable r]
    (hp : ¬ p) (hq : ¬ q) (hr : ¬ r) :
    ¬ (decide p || decide q || decide r) := by
  simp only [hp, hq, hr, decide_false, Bool.or_false, Bool.false_eq_true,
    not_false_eq_true]

theorem collectorZeroFits (capacity : Nat) (hcap : capacity < 2 ^ 63) :
    ¬ zero > JInt.wrap .i64 (capacity : Int) := by
  change ¬ (0 : Int) > (JInt.wrap .i64 (capacity : Int)).val
  exact Int.not_lt.mpr ((collectorLengthFits capacity hcap).symm ▸ Int.natCast_nonneg capacity)

theorem collectorEndFits (n : I) (capacity : Nat)
    (hsource : n.val ≤ (capacity : Int)) (hcap : capacity < 2 ^ 63) :
    ¬ n > JInt.wrap .i64 (capacity : Int) := by
  change ¬ n.val > (JInt.wrap .i64 (capacity : Int)).val
  exact Int.not_lt.mpr (Int.le_trans hsource
    (Int.le_of_eq (collectorLengthFits capacity hcap).symm))

theorem collectorStateCheck (n : I) (capacity : Nat)
    (hsource : n.val ≤ (capacity : Int)) (hcap : capacity < 2 ^ 63) :
    ¬ (one < one || zero > JInt.wrap .i64 (capacity : Int) ||
      n > JInt.wrap .i64 (capacity : Int)) :=
  noThreeChecks _ _ _ (by change ¬ (1 : Int) < 1; omega)
    (collectorZeroFits capacity hcap) (collectorEndFits n capacity hsource hcap)

theorem collectorNoSlide (n : I) (hn : 0 ≤ n.val)
    (hnew : n.val + 1 ≤ IntTy.i64.max) : ¬ zero > n + one := by
  have hfit := collectorIncrementFits n hn hnew
  have hval : (n + one).val = n.val + 1 :=
    wrapInt_of_inRange .i64 _ hfit
  change ¬ (0 : Int) > (n + one).val
  rw [hval]
  omega

theorem collectorGrowthChecks (n : I) (capacity : Nat)
    (hn : 0 ≤ n.val) (hsource : n.val ≤ (capacity : Int))
    (hcap : capacity < 2 ^ 63) (hnew : n.val + 1 ≤ IntTy.i64.max) :
    (IntTy.i64.min ≤ n.val + one.val ∧ n.val + one.val ≤ IntTy.i64.max) ∧
    (¬ (one < one || zero > JInt.wrap .i64 (capacity : Int) ||
      n > JInt.wrap .i64 (capacity : Int))) ∧
    (IntTy.i64.min ≤ zero.val + (n + one).val ∧
      zero.val + (n + one).val ≤ IntTy.i64.max) ∧
    (¬ zero > n + one) :=
  ⟨collectorIncrementFits n hn hnew, collectorStateCheck n capacity hsource hcap,
    collectorZeroAddFits (n + one), collectorNoSlide n hn hnew⟩

theorem mutableGrowendInternal_reallocate_run (s : MutableMemory α)
    (handle mem : Nat) (n : I) (source : List (Option α))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some source)
    (hn : 0 ≤ n.val) (hsource : n.val ≤ (source.length : Int))
    (hsourceCap : source.length < 2 ^ 63)
    (hnew : n.val + 1 ≤ IntTy.i64.max)
    (suggested : I)
    (hover : ∀ state : MutableMemory α,
      (mutableStorage.overallocation (JInt.wrap .i64 (source.length : Int))).run state =
        (.ok suggested, state)) :
    (growendInternal mutableStorage handle one n).run s =
      (.ok (), relocatedVectorMemory s handle n (max suggested (n + one)) source) := by
  obtain ⟨hnfit, hvalid, hzfit, hslide⟩ :=
    collectorGrowthChecks n source.length hn hsource hsourceCap hnew
  exact (growendInternal_relocation_tail s handle mem n source ha hm hnfit hvalid hzfit hslide).trans
    (relocationStorageTail_run s handle mem n source ha hm hn hsource hnew suggested hover)

theorem mutableGrowend_spare_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) (slots : List (Option α))
    (hm : s.memories[a.reference.1]? = some slots)
    (hlen : (JInt.wrap .i64 (slots.length : Int)).val = slots.length)
    (hsize : 0 ≤ a.size.val)
    (hspare : 1 ≤ a.reference.2.val ∧
      a.reference.2.val - 1 + a.size.val + 1 ≤ (slots.length : Int)) :
    (growend mutableStorage pure (growendInternal mutableStorage) handle one).run s =
      (.ok (), {s with arrays := s.arrays.set handle {a with size := a.size + one}}) := by
  have hmax : (slots.length : Int) ≤ IntTy.i64.max := by
    rw [← hlen]
    exact (JInt.wrap .i64 (slots.length : Int)).property.2
  have hoff : (a.reference.2 - one).val = a.reference.2.val - 1 := by
    change wrapInt .i64 (a.reference.2.val - 1) = a.reference.2.val - 1
    apply wrapInt_of_inRange
    have hb := a.reference.2.property
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
    omega
  have hremaining : ((JInt.wrap .i64 (slots.length : Int)) - (a.reference.2 - one)).val =
      (slots.length : Int) - (a.reference.2.val - 1) := by
    change wrapInt .i64 ((JInt.wrap .i64 (slots.length : Int)).val -
      (a.reference.2 - one).val) = _
    rw [hlen, hoff]
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hmax ⊢
    omega
  have hfree : ((JInt.wrap .i64 (slots.length : Int)) - (a.reference.2 - one) - a.size).val =
      (slots.length : Int) - (a.reference.2.val - 1) - a.size.val := by
    change wrapInt .i64
      (((JInt.wrap .i64 (slots.length : Int)) - (a.reference.2 - one)).val - a.size.val) = _
    rw [hremaining]
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hmax ⊢
    omega
  have hroom : ¬ ((JInt.wrap .i64 (slots.length : Int)) -
      (a.reference.2 - one) - a.size < one) := by
    change ¬ _ < one.val
    rw [hfree]
    change ¬ ((slots.length : Int) - (a.reference.2.val - 1) - a.size.val < 1)
    omega
  simp only [growend, mutableStorage, stateExcept_bind, stateExcept_pure,
    show (one ≥ zero) = True from propext (by decide), decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, mutableRef_run s handle a ha,
    mutableLength_run s handle a ha, memoryRead_run s a.reference.1 slots hm]
  simp only [hroom, ite_false, stateExcept_bind, mutableVector_run, ha, mutation_modify_run]

theorem jint_i64_reference_offset (offset size : I)
    (hrange : IntTy.i64.min ≤ offset.val + size.val ∧
      offset.val + size.val ≤ IntTy.i64.max) :
    (offset + (size + one) - one).val = offset.val + size.val := by
  change wrapInt .i64 (wrapInt .i64 (offset.val +
    wrapInt .i64 (size.val + 1)) - 1) = offset.val + size.val
  simp only [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at hrange ⊢
  simp at hrange ⊢
  omega

theorem mutablePush_spare_run (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) (slots : List (Option α))
    (hm : s.memories[a.reference.1]? = some slots)
    (hcapacity : slots.length < 2 ^ 63) (hsize : 0 ≤ a.size.val)
    (hspare : 1 ≤ a.reference.2.val ∧
      a.reference.2.val - 1 + a.size.val + 1 ≤ (slots.length : Int)) (x : α) :
    (mutablePush handle x).run s =
      (.ok (), {
        memories := s.memories.set a.reference.1
          (slots.set (a.reference.2.val + a.size.val - 1).toNat (some x))
        arrays := s.arrays.set handle {a with size := a.size + one}}) := by
  have hlen : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := by
    change wrapInt .i64 (slots.length : Int) = slots.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hmax : (slots.length : Int) ≤ IntTy.i64.max := by
    simp only [IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hnew : (a.size + one).val = a.size.val + 1 := by
    change wrapInt .i64 (a.size.val + 1) = a.size.val + 1
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hmax ⊢
    omega
  have hoff := jint_i64_reference_offset a.reference.2 a.size (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hmax ⊢
    omega)
  let grown : MutableMemory α :=
    {s with arrays := s.arrays.set handle {a with size := a.size + one}}
  have haLt : handle < s.arrays.length := (List.getElem?_eq_some_iff.mp ha).choose
  have hag : grown.arrays[handle]? = some {a with size := a.size + one} := by
    exact List.getElem?_set_self haLt
  have hbg : one ≤ a.size + one ∧ a.size + one ≤ a.size + one := by
    change 1 ≤ (a.size + one).val ∧ (a.size + one).val ≤ (a.size + one).val
    rw [hnew]
    omega
  have hrg : 1 ≤ (a.reference.2 + (a.size + one) - one).val ∧
      (a.reference.2 + (a.size + one) - one).val ≤ (slots.length : Int) := by
    rw [hoff]
    omega
  simp only [mutablePush, push1361, stateExcept_bind,
    mutableGrowend_spare_run s handle a ha slots hm hlen hsize hspare]
  rw [mutableLength_run grown handle _ hag]
  dsimp only
  rw [mutableSet_run grown handle _ hag slots hm _ x hbg hrg]
  simp only [stateExcept_pure, hoff]
  rfl

theorem window_set_next (xs : List β) (offset n : Nat) (v : β)
    (h : offset + n < xs.length) :
    ((xs.set (offset + n) v).drop offset).take (n + 1) =
      (xs.drop offset).take n ++ [v] := by
  rw [List.drop_set]
  simp only [show ¬ offset + n < offset by omega, ite_false, Nat.add_sub_cancel_left]
  have hn : n < (xs.drop offset).length := by simp only [List.length_drop]; omega
  rw [List.take_succ_eq_append_getElem (by simpa using hn)]
  rw [List.take_set_of_le (by omega), List.getElem_set_self]

theorem mutablePush_spare_contents (s : MutableMemory α) (handle : Nat) (a : MutableVector)
    (ha : s.arrays[handle]? = some a) (slots : List (Option α))
    (hm : s.memories[a.reference.1]? = some slots)
    (hcapacity : slots.length < 2 ^ 63) (hsize : 0 ≤ a.size.val)
    (hspare : 1 ≤ a.reference.2.val ∧
      a.reference.2.val - 1 + a.size.val + 1 ≤ (slots.length : Int)) (x : α) :
    ∃ next, (mutablePush handle x).run s = (.ok (), next) ∧
      next.contents handle = s.contents handle ++ [some x] ∧
      next.validVector handle := by
  let next : MutableMemory α := {
    memories := s.memories.set a.reference.1
      (slots.set (a.reference.2.val + a.size.val - 1).toNat (some x))
    arrays := s.arrays.set handle {a with size := a.size + one}}
  have he := mutablePush_spare_run s handle a ha slots hm hcapacity hsize hspare x
  have haLt : handle < s.arrays.length := (List.getElem?_eq_some_iff.mp ha).choose
  have hmLt : a.reference.1 < s.memories.length := (List.getElem?_eq_some_iff.mp hm).choose
  have han : next.arrays[handle]? = some {a with size := a.size + one} :=
    List.getElem?_set_self haLt
  have hmn : next.memories[a.reference.1]? =
      some (slots.set (a.reference.2.val + a.size.val - 1).toNat (some x)) :=
    List.getElem?_set_self hmLt
  have hnew : (a.size + one).val = a.size.val + 1 := by
    change wrapInt .i64 (a.size.val + 1) = a.size.val + 1
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hcount : (a.size + one).val.toNat = a.size.val.toNat + 1 := by rw [hnew]; omega
  have hindex : (a.reference.2.val + a.size.val - 1).toNat =
      (a.reference.2.val - 1).toNat + a.size.val.toNat := by omega
  have hwindow : (a.reference.2.val - 1).toNat + a.size.val.toNat < slots.length := by omega
  refine ⟨next, he, ?_, ?_⟩
  · simp only [MutableMemory.contents, ha, han, hm, hmn, Option.getD_some,
      hcount, hindex]
    exact window_set_next slots _ _ _ hwindow
  · simp only [MutableMemory.validVector, han, hmn, List.length_set, hnew]
    exact ⟨by omega, hspare.1, by omega, hcapacity⟩

theorem relocatedVector_layout (s : MutableMemory α) (handle : Nat)
    (n capacity : I) (source : List (Option α))
    (ha : handle < s.arrays.length) (hn : 0 ≤ n.val) (hcap : n.val ≤ capacity.val)
    (hsource : n.val ≤ (source.length : Int)) :
    let next := relocatedVectorMemory s handle n capacity source
    let slots := source.take n.val.toNat ++ (List.replicate capacity.val.toNat none).drop n.val.toNat
    next.arrays[handle]? = some ⟨(s.memories.length, one), n⟩ ∧
    next.memories[s.memories.length]? = some slots ∧
    slots.length = capacity.val.toNat ∧
    next.contents handle = source.take n.val.toNat := by
  intro next slots
  have han : next.arrays[handle]? = some ⟨(s.memories.length, one), n⟩ :=
    List.getElem?_set_self ha
  have hmn : next.memories[s.memories.length]? = some slots := by
    apply List.getElem?_set_self
    simp only [List.length_append, List.length_singleton]
    omega
  have htake : (source.take n.val.toNat).length = n.val.toNat := by
    rw [List.length_take]
    omega
  refine ⟨han, hmn, ?_, ?_⟩
  · simp only [slots, List.length_append, List.length_take, List.length_drop,
      List.length_replicate]
    omega
  · simp only [MutableMemory.contents, han, hmn, Option.getD_some,
      show one.val = 1 from rfl, Int.sub_self, Int.toNat_zero, List.drop_zero]
    change (source.take n.val.toNat ++ _).take n.val.toNat = _
    simpa only [htake] using (List.take_append_length
      (l₁ := source.take n.val.toNat)
      (l₂ := (List.replicate capacity.val.toNat none).drop n.val.toNat))

@[simp] theorem jint_i64_sub_self (x : I) : x - x = zero := by
  apply Subtype.ext
  change wrapInt .i64 (x.val - x.val) = 0
  rw [Int.sub_self]
  rfl

theorem mutableGrowend_full_run (s : MutableMemory α) (handle mem : Nat) (n : I)
    (source : List (Option α))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some source) (hn : 0 ≤ n.val)
    (hfull : (source.length : Int) = n.val) (hnew : n.val + 1 ≤ IntTy.i64.max)
    (suggested : I)
    (hover : ∀ state : MutableMemory α,
      (mutableStorage.overallocation (JInt.wrap .i64 (source.length : Int))).run state =
        (.ok suggested, state)) :
    let moved := relocatedVectorMemory s handle n (max suggested (n + one)) source
    (growend mutableStorage pure (growendInternal mutableStorage) handle one).run s =
      (.ok (), {moved with arrays := (moved.arrays.set handle
        ⟨(s.memories.length, one), n + one⟩)}) := by
  intro moved
  have hsource : n.val ≤ (source.length : Int) := by omega
  have hsourceCap : source.length < 2 ^ 63 := by
    have hb := n.property.2
    change n.val ≤ 9223372036854775807 at hb
    change source.length < 9223372036854775808
    omega
  have hleneq : JInt.wrap .i64 (source.length : Int) = n := by
    apply Subtype.ext
    change wrapInt .i64 (source.length : Int) = n.val
    rw [hfull]
    exact wrapInt_of_inRange .i64 n.val n.property
  have hi := mutableGrowendInternal_reallocate_run s handle mem n source ha hm hn
    hsource hsourceCap hnew suggested hover
  have ham : moved.arrays[handle]? = some ⟨(s.memories.length, one), n⟩ :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp ha).choose
  simp only [mutableStorage] at hi
  simp only [growend, mutableStorage, stateExcept_bind, stateExcept_pure,
    show (one ≥ zero) = True from propext (by decide), decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, mutableRef_run s handle ⟨(mem, one), n⟩ ha,
    mutableLength_run s handle ⟨(mem, one), n⟩ ha, memoryRead_run s mem source hm,
    hleneq, show one - one = zero from rfl, jint_i64_sub_zero, jint_i64_sub_self,
    show zero < one from (by decide), ite_true, hi]
  dsimp only [moved] at ham
  rw [mutableVector_run]
  simp only [ham, mutation_modify_run]
  rfl

def CollectorState (s : MutableMemory α) (handle : Nat) (n : I) : Prop :=
  ∃ (mem : Nat) (slots : List (Option α)),
    s.arrays[handle]? = some ⟨(mem, one), n⟩ ∧ s.memories[mem]? = some slots ∧
    0 ≤ n.val ∧ n.val ≤ (slots.length : Int) ∧ slots.length < 2 ^ 63

theorem collectorState_valid (s : MutableMemory α) (handle : Nat) (n : I)
    (h : CollectorState s handle n) : s.validVector handle := by
  obtain ⟨mem, slots, ha, hm, hn, hend, hcap⟩ := h
  simp only [MutableMemory.validVector, ha, hm, show one.val = 1 from rfl]
  exact ⟨hn, by decide, by omega, hcap⟩

theorem mutablePush_spare_collector (s : MutableMemory α) (handle mem : Nat)
    (n : I) (slots : List (Option α))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some slots)
    (hcapacity : slots.length < 2 ^ 63) (hn : 0 ≤ n.val)
    (hspare : n.val + 1 ≤ (slots.length : Int)) (x : α) :
    ∃ next, (mutablePush handle x).run s = (.ok (), next) ∧
      next.contents handle = s.contents handle ++ [some x] ∧
      CollectorState next handle (n + one) := by
  have hr : 1 ≤ one.val ∧ one.val - 1 + n.val + 1 ≤ (slots.length : Int) := by
    change 1 ≤ (1 : Int) ∧ 1 - 1 + n.val + 1 ≤ (slots.length : Int)
    omega
  obtain ⟨next, he, hc, _⟩ := mutablePush_spare_contents s handle ⟨(mem, one), n⟩
    ha slots hm hcapacity hn hr x
  have hs := mutablePush_spare_run s handle ⟨(mem, one), n⟩ ha slots hm hcapacity hn hr x
  rw [he] at hs
  have hsnext := congrArg Prod.snd hs
  dsimp only at hsnext
  have haLt := (List.getElem?_eq_some_iff.mp ha).choose
  have hmLt := (List.getElem?_eq_some_iff.mp hm).choose
  have hnv : (n + one).val = n.val + 1 := by
    change wrapInt .i64 (n.val + 1) = n.val + 1
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ n.val + 1 ∧ n.val + 1 ≤ 9223372036854775807
    omega
  refine ⟨next, he, hc, ?_⟩
  rw [hsnext]
  refine ⟨mem, slots.set (one.val + n.val - 1).toNat (some x),
    List.getElem?_set_self haLt, List.getElem?_set_self hmLt, ?_, ?_, ?_⟩
  · rw [hnv]; omega
  · simp only [hnv, List.length_set]; omega
  · simpa only [List.length_set] using hcapacity

theorem mutablePush_full_contents (s : MutableMemory α) (handle mem : Nat) (n : I)
    (source : List (Option α))
    (ha : s.arrays[handle]? = some ⟨(mem, one), n⟩)
    (hm : s.memories[mem]? = some source) (hn : 0 ≤ n.val)
    (hfull : (source.length : Int) = n.val) (hnew : n.val + 1 ≤ IntTy.i64.max)
    (x : α) :
    ∃ next, (mutablePush handle x).run s = (.ok (), next) ∧
      next.contents handle = s.contents handle ++ [some x] ∧
      CollectorState next handle (n + one) := by
  obtain ⟨suggested, hover⟩ := mutableOverallocation_run (α := α)
    (JInt.wrap .i64 (source.length : Int))
  let capacity := max suggested (n + one)
  let moved := relocatedVectorMemory s handle n capacity source
  let slots := source.take n.val.toNat ++ (List.replicate capacity.val.toNat none).drop n.val.toNat
  have hnv : (n + one).val = n.val + 1 := by
    change wrapInt .i64 (n.val + 1) = n.val + 1
    apply wrapInt_of_inRange
    exact ⟨by change -9223372036854775808 ≤ n.val + 1; omega, hnew⟩
  have hcapge : n.val + 1 ≤ capacity.val := by
    rw [← hnv]
    change (n + one).val ≤ max suggested.val (n + one).val
    exact Int.le_max_right _ _
  have hcap : capacity.val.toNat < 2 ^ 63 := by
    have hb := capacity.property.2
    change capacity.val ≤ 9223372036854775807 at hb
    change capacity.val.toNat < 9223372036854775808
    omega
  have hlayout := relocatedVector_layout s handle n capacity source
    (List.getElem?_eq_some_iff.mp ha).choose hn (by omega) (by omega)
  change moved.arrays[handle]? = some ⟨(s.memories.length, one), n⟩ ∧
    moved.memories[s.memories.length]? = some slots ∧
    slots.length = capacity.val.toNat ∧ moved.contents handle = source.take n.val.toNat at hlayout
  obtain ⟨han, hmn, hlength, hcontents⟩ := hlayout
  have hslotsCap : slots.length < 2 ^ 63 := by omega
  have hspare : 1 ≤ one.val ∧ one.val - 1 + n.val + 1 ≤ (slots.length : Int) := by
    change 1 ≤ (1 : Int) ∧ 1 - 1 + n.val + 1 ≤ (slots.length : Int)
    omega
  have hlen : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := by
    change wrapInt .i64 (slots.length : Int) = slots.length
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ (slots.length : Int) ∧
      (slots.length : Int) ≤ 9223372036854775807
    omega
  have hg := mutableGrowend_full_run s handle mem n source ha hm hn hfull hnew suggested hover
  dsimp only at hg
  have hgr := mutableGrowend_spare_run moved handle
    ⟨(s.memories.length, one), n⟩ han slots hmn hlen hn hspare
  have hsame : (mutablePush handle x).run s = (mutablePush handle x).run moved := by
    simp only [mutablePush, push1361, stateExcept_bind, hg, hgr]
    rfl
  obtain ⟨next, he, hc, hv⟩ := mutablePush_spare_collector moved handle
    s.memories.length n slots han hmn hslotsCap hn (by
      change 1 ≤ (1 : Int) ∧ 1 - 1 + n.val + 1 ≤ (slots.length : Int) at hspare
      omega) x
  have horiginal : s.contents handle = source.take n.val.toNat := by
    simp only [MutableMemory.contents, ha, hm, Option.getD_some, show one.val = 1 from rfl,
      Int.sub_self, Int.toNat_zero, List.drop_zero]
  exact ⟨next, hsame.trans he, by simpa only [hcontents, horiginal] using hc, hv⟩

theorem mutablePush_collector (s : MutableMemory α) (handle : Nat) (n : I)
    (hstate : CollectorState s handle n) (hnew : n.val + 1 ≤ IntTy.i64.max) (x : α) :
    ∃ next, (mutablePush handle x).run s = (.ok (), next) ∧
      next.contents handle = s.contents handle ++ [some x] ∧
      CollectorState next handle (n + one) := by
  obtain ⟨mem, slots, ha, hm, hn, hsource, hcap⟩ := hstate
  by_cases hspare : n.val + 1 ≤ (slots.length : Int)
  · exact mutablePush_spare_collector s handle mem n slots ha hm hcap hn hspare x
  · exact mutablePush_full_contents s handle mem n slots ha hm hn (by omega) hnew x

theorem collectUnknown_loop (xs : List α) (s : MutableMemory α) (handle : Nat) (n : I)
    (hstate : CollectorState s handle n)
    (hsize : n.val + (xs.length : Int) ≤ IntTy.i64.max) :
    ∃ (next : MutableMemory α) (len : I),
      (forIn xs () (fun x _ => do
        mutablePush handle x
        pure (ForInStep.yield ()))).run s = (.ok (), next) ∧
      next.contents handle = s.contents handle ++ xs.map some ∧
      CollectorState next handle len ∧ len.val = n.val + (xs.length : Int) := by
  induction xs generalizing s n with
  | nil =>
    exact ⟨s, n, rfl, by simp, hstate, by simp⟩
  | cons x xs ih =>
    have hnew : n.val + 1 ≤ IntTy.i64.max := by
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hsize
      omega
    have hn : 0 ≤ n.val := hstate.choose_spec.choose_spec.2.2.1
    have hnv : (n + one).val = n.val + 1 := by
      change wrapInt .i64 (n.val + 1) = n.val + 1
      apply wrapInt_of_inRange
      exact ⟨by change -9223372036854775808 ≤ n.val + 1; omega, hnew⟩
    obtain ⟨mid, hpush, hc, hmid⟩ := mutablePush_collector s handle n hstate hnew x
    obtain ⟨next, len, hrest, hcontents, hnext, hlen⟩ :=
      ih mid (n + one) hmid (by
        rw [hnv]
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hsize
        omega)
    refine ⟨next, len, ?_, ?_, hnext, ?_⟩
    · simp only [List.forIn_cons, stateExcept_bind, hpush, stateExcept_pure]
      exact hrest
    · rw [hcontents, hc]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]
    · rw [hnv] at hlen
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
      omega

def allocatedEmptyVector (s : MutableMemory α) : MutableMemory α := {
  memories := s.memories ++ [[]]
  arrays := s.arrays ++ [⟨(s.memories.length, one), zero⟩]}

theorem mutableAllocate_empty_run (s : MutableMemory α) :
    (mutableAllocate 0 zero).run s = (.ok s.arrays.length, allocatedEmptyVector s) := rfl

theorem allocatedEmptyVector_state (s : MutableMemory α) :
    CollectorState (allocatedEmptyVector s) s.arrays.length zero ∧
      (allocatedEmptyVector s).contents s.arrays.length = [] := by
  have ha : (allocatedEmptyVector s).arrays[s.arrays.length]? =
      some ⟨(s.memories.length, one), zero⟩ := by simp [allocatedEmptyVector]
  have hm : (allocatedEmptyVector s).memories[s.memories.length]? = some [] := by
    simp [allocatedEmptyVector]
  constructor
  · exact ⟨s.memories.length, [], ha, hm, by decide,
      by change (0 : Int) ≤ 0; decide, by change (0 : Nat) < 2 ^ 63; decide⟩
  · simp only [MutableMemory.contents, ha, hm, Option.getD_some, List.drop_nil, List.take_nil]

def UnknownTypedCollectionSpec : Prop :=
  ∀ (α : Type) (xs : List α) (s : MutableMemory α),
    xs.length < 2 ^ 63 →
    ∃ next,
      (collectUnknown (mutableAllocate 0 zero) mutablePush xs).run s =
        (.ok s.arrays.length, next) ∧
      next.contents s.arrays.length = xs.map some ∧
      next.validVector s.arrays.length

theorem unknownTypedCollectionSpec : UnknownTypedCollectionSpec := by
  intro α xs s hsize
  obtain ⟨hstate, hempty⟩ := allocatedEmptyVector_state s
  obtain ⟨next, len, hloop, hc, hnext, _⟩ := collectUnknown_loop xs (allocatedEmptyVector s)
    s.arrays.length zero hstate (by
      change 0 + (xs.length : Int) ≤ 9223372036854775807
      change xs.length < 9223372036854775808 at hsize
      omega)
  refine ⟨next, ?_, ?_, collectorState_valid next s.arrays.length len hnext⟩
  · simp only [collectUnknown, stateExcept_bind, mutableAllocate_empty_run, hloop, stateExcept_pure]
  · simpa only [hempty, List.nil_append] using hc

def elementConversion (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (x : β) : Except Error α :=
  if already x then .ok (asTyped x) else convert x

def collectingPush (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (handle : Nat) (x : β) : MutationM α Unit := do
  let _ ← JuliaLean.base.array.push already asTyped
    (fun x => stateExceptLift (convert x))
    (push1361 (growend mutableStorage pure (growendInternal mutableStorage))
      mutableLength mutableSet) handle x
  pure ()

theorem collectingPush_run (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (s : MutableMemory α) (handle : Nat) (x : β) :
    (collectingPush already asTyped convert handle x).run s =
      match elementConversion already asTyped convert x with
      | .error e => (.error e, s)
      | .ok y => (mutablePush handle y).run s := by
  cases ha : already x with
  | true =>
    simp only [collectingPush, JuliaLean.base.array.push, elementConversion, ha,
      ite_true, stateExcept_bind, stateExcept_pure, mutablePush]
  | false =>
    simp only [collectingPush, JuliaLean.base.array.push, elementConversion, ha,
      Bool.false_eq_true, ite_false, stateExcept_bind, stateExceptLift_run, mutablePush]
    cases convert x <;> rfl

theorem convertingCollectionLoop (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (xs : List β)
    (s : MutableMemory α) (handle : Nat) (n : I)
    (hstate : CollectorState s handle n)
    (hsize : n.val + (xs.length : Int) ≤ IntTy.i64.max) :
    let conversion := xs.mapM (elementConversion already asTyped convert)
    let action := forIn xs () (fun x _ => do
      collectingPush already asTyped convert handle x
      pure (ForInStep.yield ()))
    (∀ ys, conversion = .ok ys →
      ∃ next len, action.run s = (.ok (), next) ∧
        next.contents handle = s.contents handle ++ ys.map some ∧
        CollectorState next handle len) ∧
    (∀ e, conversion = .error e → (action.run s).1 = .error e) := by
  dsimp only
  induction xs generalizing s n with
  | nil =>
    constructor
    · intro ys hy
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hy
      subst ys
      exact ⟨s, n, rfl, by simp, hstate⟩
    · intro e he
      simp [List.mapM_nil, Pure.pure, Except.pure] at he
  | cons x xs ih =>
    cases hx : elementConversion already asTyped convert x with
    | error e =>
      constructor
      · intro ys hy
        simp [List.mapM_cons, hx, Bind.bind, Except.bind] at hy
      · intro err he
        have heq : e = err := by simpa [List.mapM_cons, hx, Bind.bind, Except.bind] using he
        subst err
        simp only [List.forIn_cons, stateExcept_bind, collectingPush_run, hx]
    | ok y =>
      have hn : 0 ≤ n.val := hstate.choose_spec.choose_spec.2.2.1
      have hnew : n.val + 1 ≤ IntTy.i64.max := by
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hsize
        omega
      have hnv : (n + one).val = n.val + 1 := by
        change wrapInt .i64 (n.val + 1) = n.val + 1
        exact wrapInt_of_inRange .i64 _ ⟨by change -9223372036854775808 ≤ n.val + 1; omega, hnew⟩
      obtain ⟨mid, hpush, hc, hmid⟩ := mutablePush_collector s handle n hstate hnew y
      have htail := ih mid (n + one) hmid (by
        rw [hnv]
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hsize
        omega)
      constructor
      · intro ys hy
        cases hr : xs.mapM (elementConversion already asTyped convert) with
        | error e => simp [List.mapM_cons, hx, hr, Bind.bind, Except.bind] at hy
        | ok zs =>
          have hys : y :: zs = ys := by
            simpa [List.mapM_cons, hx, hr, Bind.bind, Except.bind, Functor.map,
              Except.map, Pure.pure, Except.pure] using hy
          subst ys
          obtain ⟨next, len, hrest, hcontents, hnext⟩ := htail.1 zs hr
          refine ⟨next, len, ?_, ?_, hnext⟩
          · simp only [List.forIn_cons, stateExcept_bind, collectingPush_run, hx, hpush,
              stateExcept_pure]
            exact hrest
          · rw [hcontents, hc]
            simp only [List.map_cons, List.append_assoc, List.singleton_append]
      · intro e he
        cases hr : xs.mapM (elementConversion already asTyped convert) with
        | error err =>
          have heq : err = e := by
            simpa [List.mapM_cons, hx, hr, Bind.bind, Except.bind, Functor.map, Except.map] using he
          subst e
          simp only [List.forIn_cons, stateExcept_bind, collectingPush_run, hx, hpush,
            stateExcept_pure]
          exact htail.2 err hr
        | ok zs => simp [List.mapM_cons, hx, hr, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at he

def UnknownCollectionSpec : Prop :=
  ∀ (α β : Type) (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (xs : List β) (s : MutableMemory α),
    xs.length < 2 ^ 63 →
    let conversion := xs.mapM (elementConversion already asTyped convert)
    let result := (collectTyped (fun _ => ())
      (fun (_ : Type) itr (_ : Unit) => collectUnknown (mutableAllocate 0 zero)
        (collectingPush already asTyped convert) itr) α xs).run s
    (∀ ys, conversion = .ok ys →
      ∃ next, result = (.ok s.arrays.length, next) ∧
        next.contents s.arrays.length = ys.map some ∧
        next.validVector s.arrays.length) ∧
    (∀ e, conversion = .error e → result.1 = .error e)

theorem unknownCollectionSpec : UnknownCollectionSpec := by
  intro α β already asTyped convert xs s hsize
  dsimp only
  obtain ⟨hstate, hempty⟩ := allocatedEmptyVector_state s
  have hp := convertingCollectionLoop already asTyped convert xs (allocatedEmptyVector s)
    s.arrays.length zero hstate (by
      change 0 + (xs.length : Int) ≤ 9223372036854775807
      change xs.length < 9223372036854775808 at hsize
      omega)
  dsimp only at hp
  constructor
  · intro ys hy
    obtain ⟨next, len, he, hc, hv⟩ := hp.1 ys hy
    refine ⟨next, ?_, ?_, collectorState_valid next s.arrays.length len hv⟩
    · simp only [collectTyped, collectUnknown, stateExcept_bind, mutableAllocate_empty_run,
        he, stateExcept_pure]
    · simpa only [hempty, List.nil_append] using hc
  · intro e he
    have herr := hp.2 e he
    simp only [collectTyped, collectUnknown, stateExcept_bind, mutableAllocate_empty_run]
    cases hrun : (forIn xs () (fun x _ => do
      collectingPush already asTyped convert s.arrays.length x
      pure (ForInStep.yield ()))).run (allocatedEmptyVector s) with
    | mk result next =>
      cases result with
      | error err =>
        have heq : err = e := Except.error.inj (by simpa only [hrun] using herr)
        simp only [heq]
      | ok value => simp only [hrun] at herr; cases herr

def UnknownIntegerCollectionSpec : Prop :=
  ∀ (T S : IntTy) (xs : List (JInt S)) (s : MutableMemory (JInt T)),
    xs.length < 2 ^ 63 →
    let convert := fun x : JInt S =>
      (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)
    let result := (collectUnknown (mutableAllocate 0 zero)
      (collectingPush (fun _ => false) (fun x : JInt S => JInt.wrap T x.val) convert) xs).run s
    ((∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max) →
      ∃ next, result = (.ok s.arrays.length, next) ∧
        next.contents s.arrays.length = xs.map (fun x => some (JInt.wrap T x.val)) ∧
        next.validVector s.arrays.length) ∧
    ((∃ x ∈ xs, ¬(T.min ≤ x.val ∧ x.val ≤ T.max)) →
      result.1 = .error .inexact)

theorem unknownIntegerCollectionSpec : UnknownIntegerCollectionSpec := by
  intro T S xs s hsize
  dsimp only
  have hp := unknownCollectionSpec (JInt T) (JInt S) (fun _ => false)
    (fun x => JInt.wrap T x.val)
    (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)) xs s hsize
  dsimp only at hp
  constructor
  · intro hfit
    have hsuccess :
        xs.mapM (elementConversion (fun _ => false) (fun x : JInt S => JInt.wrap T x.val)
          (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))) =
          .ok (xs.map (fun x : JInt S => JInt.wrap T x.val)) := by
      change xs.mapM (fun x : JInt S =>
        (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)) = _
      exact bitinteger_array_mapM_success T xs hfit
    simpa only [collectTyped, List.map_map, Function.comp_def] using
      hp.1 (xs.map (fun x : JInt S => JInt.wrap T x.val)) hsuccess
  · intro hbad
    have hfailure :
        xs.mapM (elementConversion (fun _ => false) (fun x : JInt S => JInt.wrap T x.val)
          (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact))) =
          .error .inexact := by
      change xs.mapM (fun x : JInt S =>
        (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)) = _
      exact bitinteger_array_mapM_failure T xs hbad
    exact hp.2 .inexact hfailure

def CompleteUnknownCollectionSpec : Prop :=
  UnknownTypedCollectionSpec ∧ UnknownCollectionSpec ∧ UnknownIntegerCollectionSpec

theorem completeUnknownCollectionSpec : CompleteUnknownCollectionSpec :=
  ⟨unknownTypedCollectionSpec, unknownCollectionSpec, unknownIntegerCollectionSpec⟩

def freshVectorAllocation {Tag α : Type} (target : Tag) (n : Nat) (heap : VectorHeap α) :
    Except Error (HeapArray Tag × VectorHeap α) :=
  .ok (⟨heap.length, target, [n], [(1, n)]⟩, heap ++ [List.replicate n none])

theorem heapVectorAllocate_run {Tag α : Type} (target : Tag) (n : I) (heap : VectorHeap α) :
    (heapVectorAllocate target n).run heap =
      if n.val < 0 then .error (.argument "invalid Array dimensions")
      else freshVectorAllocation target n.val.toNat heap := by
  by_cases hnegative : n.val < 0
  · simp only [heapVectorAllocate, hnegative, ite_true, vector_throw_run]
  · have hn : n.val.toNat < 2 ^ 63 := by
      have hb := n.property.2
      change n.val ≤ 9223372036854775807 at hb
      change n.val.toNat < 9223372036854775808
      omega
    have hd : heapDimensionsFit [n.val.toNat] = true := by
      simp [heapDimensionsFit, hn]
    simp only [heapVectorAllocate, hnegative, ite_false]
    rw [heapAllocateArray_run target [n.val.toNat] heap hd (by simpa using hn)]
    simp [freshVectorAllocation]

/-- `Int(len)` keeps a representable Integer value and rejects an out-of-range one. -/
def CollectorIntLaw {Z : Type} (value : Z → Int) (toInt : Z → Except Error I) : Prop :=
  ∀ z, toInt z =
    if IntTy.i64.min ≤ value z ∧ value z ≤ IntTy.i64.max
    then .ok (JInt.wrap .i64 (value z)) else .error .inexact

def EmptyCollectorAllocationSpec : Prop :=
  ∀ (Tag α : Type) (target : Tag) (heap : VectorHeap α),
    (arrayForUnknown (m := VectorM α) (heapVectorAllocate (α := α)) target).run heap =
      freshVectorAllocation target 0 heap

theorem emptyCollectorAllocationSpec : EmptyCollectorAllocationSpec := by
  intro Tag α target heap
  simp only [arrayForUnknown, heapVectorAllocate_run, show zero.val = 0 from rfl,
    Int.lt_irrefl, ite_false, Int.toNat_zero]

def IntegerCollectorAllocationSpec : Prop :=
  ∀ (Tag α Z : Type) (value : Z → Int) (toInt : Z → Except Error I),
    CollectorIntLaw value toInt →
    ∀ (target : Tag) (z : Z) (heap : VectorHeap α),
    (arrayForLength (fun x => (liftM (toInt x) : VectorM α I))
      (heapVectorAllocate (α := α)) target z).run heap =
      if IntTy.i64.min ≤ value z ∧ value z ≤ IntTy.i64.max then
        if value z < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target (value z).toNat heap
      else .error .inexact

theorem integerCollectorAllocationSpec : IntegerCollectorAllocationSpec := by
  intro Tag α Z value toInt hconvert target z heap
  simp only [arrayForLength, vector_bind_run, vector_lift_run]
  rw [hconvert z]
  by_cases hfit : IntTy.i64.min ≤ value z ∧ value z ≤ IntTy.i64.max
  · have hv : (JInt.wrap .i64 (value z)).val = value z :=
      wrapInt_of_inRange .i64 (value z) hfit
    simp only [hfit, and_self, ite_true, Except.map]
    rw [heapVectorAllocate_run]
    simp only [hv]
  · simp only [hfit, ite_false, Except.map]

def BitIntegerCollectorAllocationSpec : Prop :=
  ∀ (Tag α : Type) (S : IntTy) (target : Tag) (n : JInt S) (heap : VectorHeap α),
    (arrayForLength
      (fun x : JInt S => (liftM ((JuliaLean.base.int.convert .i64 x).mapError
        (fun _ => Error.inexact)) : VectorM α I))
      (heapVectorAllocate (α := α)) target n).run heap =
      if IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max then
        if n.val < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target n.val.toNat heap
      else .error .inexact

theorem bitIntegerCollectorAllocationSpec : BitIntegerCollectorAllocationSpec := by
  intro Tag α S target n heap
  apply integerCollectorAllocationSpec Tag α (JInt S) Subtype.val
    (fun x => (JuliaLean.base.int.convert .i64 x).mapError (fun _ => Error.inexact))
  intro x
  exact bitinteger_array_conversion .i64 x

def CompleteCollectorAllocationSpec : Prop :=
  EmptyCollectorAllocationSpec ∧ IntegerCollectorAllocationSpec ∧
    BitIntegerCollectorAllocationSpec

theorem completeCollectorAllocationSpec : CompleteCollectorAllocationSpec :=
  ⟨emptyCollectorAllocationSpec, integerCollectorAllocationSpec,
    bitIntegerCollectorAllocationSpec⟩

def SimilarAllocationLaw {C Tag α : Type}
    (similar : C → Tag → List I → VectorM α (HeapArray Tag)) : Prop :=
  ∀ c target dims heap, (∀ dim ∈ dims, 0 ≤ dim.val) →
    (dims.map (fun dim => dim.val.toNat)).prod < 2 ^ 63 →
    (similar c target dims).run heap =
      let shape := dims.map (fun dim => dim.val.toNat)
      .ok (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
        heap ++ [List.replicate shape.prod none])

theorem nativeSimilarAllocationLaw (C Tag α : Type) :
    SimilarAllocationLaw (C := C) (Tag := Tag) (α := α)
      (fun c target dims => similar419 (heapAllocateIntDims target) c dims) := by
  intro c target dims heap hnonnegative hprod
  have hnegative : dims.any (fun dim => decide (dim.val < 0)) = false := by
    apply List.any_eq_false.mpr
    intro dim hd
    simpa only [decide_eq_true_eq] using Int.not_lt.mpr (hnonnegative dim hd)
  have hfit : heapDimensionsFit (dims.map (fun dim => dim.val.toNat)) = true := by
    apply List.all_eq_true.mpr
    intro n hn
    obtain ⟨dim, hd, rfl⟩ := List.mem_map.mp hn
    simp only [decide_eq_true_eq]
    have hu := dim.property.2
    change dim.val ≤ 9223372036854775807 at hu
    change dim.val.toNat < 9223372036854775808
    omega
  simp only [similar419, heapAllocateIntDims, hnegative, Bool.false_eq_true, ite_false]
  exact heapAllocateArray_run target _ heap hfit hprod

def UnknownSimilarInterfaceSpec : Prop :=
  ∀ (C Tag α X : Type)
    (similar : C → Tag → I → VectorM α (HeapArray Tag)),
    (∀ c target n heap, 0 ≤ n.val →
      (similar c target n).run heap =
        freshVectorAllocation target n.val.toNat heap) →
    ∀ (container : C) (target : Tag) (itr : X) (heap : VectorHeap α),
    (similarForUnknown similar container target itr).run heap =
      freshVectorAllocation target 0 heap

theorem unknownSimilarInterfaceSpec : UnknownSimilarInterfaceSpec := by
  intro C Tag α X similar hlaw container target itr heap
  have h := hlaw container target zero heap (by change (0 : Int) ≤ 0; omega)
  simpa only [similarForUnknown, show zero.val = 0 from rfl, Int.toNat_zero] using h

def UnknownSimilarNativeSpec : Prop :=
  ∀ (SourceTag Tag α X : Type) (container : HeapArray SourceTag)
    (target : Tag) (itr : X) (heap : VectorHeap α),
    (similarForUnknown
      (fun c t n => JuliaLean.base.abstractarray.similarTypeVarargs
        (fun c t dims => similar419 (heapAllocateIntDims (α := α) t) c dims)
        c t [n]) container target itr).run heap =
      .ok (⟨heap.length, target, [0], [(1, 0)]⟩, heap ++ [[]])

theorem unknownSimilarNativeSpec : UnknownSimilarNativeSpec := by
  intro SourceTag Tag α X container target itr heap
  have h := nativeSimilarAllocationLaw (HeapArray SourceTag) Tag α
    container target [zero] heap
    (by
      intro dim hd
      simp only [List.mem_singleton] at hd
      subst dim
      change (0 : Int) ≤ 0
      omega)
    (by decide)
  simpa only [similarForUnknown, JuliaLean.base.abstractarray.similarTypeVarargs,
    List.map_cons, List.map_nil, show zero.val = 0 from rfl, Int.toNat_zero,
    List.prod_cons, List.prod_nil, Nat.zero_mul, List.replicate_zero] using h

def CompleteUnknownSimilarSpec : Prop :=
  UnknownSimilarInterfaceSpec ∧ UnknownSimilarNativeSpec

theorem completeUnknownSimilarSpec : CompleteUnknownSimilarSpec :=
  ⟨unknownSimilarInterfaceSpec, unknownSimilarNativeSpec⟩

def freshShapeAllocation {Tag α : Type} (target : Tag) (shape : List Nat)
    (heap : VectorHeap α) : Except Error (HeapArray Tag × VectorHeap α) :=
  .ok (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
    heap ++ [List.replicate shape.prod none])

def collectedShape {Tag α : Type} (target : Tag) (shape : List Nat)
    (values : List α) (heap : VectorHeap α) : HeapArray Tag × VectorHeap α :=
  (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
    heap ++ [values.map some])

/-- The documented equal-size iterable-copy interface includes conversion and the frame rule. -/
def SizedCopyLaw {Tag α β X : Type} (values : X → List β)
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)) : Prop :=
  ∀ dest itr heap slots, heap[dest.handle]? = some slots →
    dest.dimensions.prod = slots.length → slots.length = (values itr).length →
    slots.length < 2 ^ 63 →
    (copy dest itr).run heap =
      ((values itr).mapM convert).map
        (fun converted => (dest, heap.set dest.handle (converted.map some)))

theorem sizedCopy_fresh {Tag α β X : Type} (values : X → List β)
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (hcopy : SizedCopyLaw values convert copy) (target : Tag) (shape : List Nat)
    (itr : X) (heap : VectorHeap α) (hlen : shape.prod = (values itr).length)
    (hsize : shape.prod < 2 ^ 63) :
    (copy ⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩ itr).run
      (heap ++ [List.replicate shape.prod none]) =
      ((values itr).mapM convert).map
        (fun converted => collectedShape target shape converted heap) := by
  have h := hcopy ⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩
    itr (heap ++ [List.replicate shape.prod none]) (List.replicate shape.prod none)
    (by simp) (by simp) (by simpa using hlen) (by simpa using hsize)
  simpa only [List.set_append, Nat.lt_irrefl, ite_false, Nat.sub_self,
    List.set_cons_zero, collectedShape] using h

def intDimensionShape (dims : List I) : Except Error (List Nat) :=
  if dims.any (fun dim => decide (dim.val < 0)) then
    .error (.argument "invalid Array dimensions")
  else
    let shape := dims.map (fun dim => dim.val.toNat)
    if shape.prod < 2 ^ 63 then .ok shape
    else .error (.argument "invalid Array dimensions")

theorem intDimensionShape_bound (dims : List I) (shape : List Nat)
    (h : intDimensionShape dims = .ok shape) : shape.prod < 2 ^ 63 := by
  cases hnegative : dims.any (fun dim => decide (dim.val < 0)) with
  | true =>
    simp only [intDimensionShape, hnegative, ite_true] at h
    cases h
  | false =>
    simp only [intDimensionShape, hnegative, Bool.false_eq_true, ite_false] at h
    by_cases hprod : (dims.map (fun dim => dim.val.toNat)).prod < 2 ^ 63
    · simp only [hprod, ite_true] at h
      rw [← Except.ok.inj h]
      exact hprod
    · simp only [hprod, ite_false] at h
      cases h

theorem intDimensionsFit (dims : List I) :
    heapDimensionsFit (dims.map (fun dim => dim.val.toNat)) = true := by
  apply List.all_eq_true.mpr
  intro n hn
  obtain ⟨dim, hd, rfl⟩ := List.mem_map.mp hn
  simp only [decide_eq_true_eq]
  have hu := dim.property.2
  change dim.val ≤ 9223372036854775807 at hu
  change dim.val.toNat < 9223372036854775808
  omega

theorem heapAllocateIntDims_run {Tag α : Type} (target : Tag) (dims : List I)
    (heap : VectorHeap α) :
    (heapAllocateIntDims target dims).run heap =
      (intDimensionShape dims).bind (fun shape => freshShapeAllocation target shape heap) := by
  by_cases hnegative : dims.any (fun dim => decide (dim.val < 0)) = true
  · simp only [heapAllocateIntDims, intDimensionShape, hnegative, ite_true,
      vector_bind_run, vector_throw_run, Except.bind] <;> rfl
  · have hfalse : dims.any (fun dim => decide (dim.val < 0)) = false :=
      Bool.eq_false_iff.mpr hnegative
    simp only [heapAllocateIntDims, intDimensionShape, hfalse,
      Bool.false_eq_true, ite_false]
    by_cases hprod : (dims.map (fun dim => dim.val.toNat)).prod < 2 ^ 63
    · rw [heapAllocateArray_run target _ heap (intDimensionsFit dims) hprod]
      simp only [hprod, ite_true, Except.bind, freshShapeAllocation]
    · rw [heapAllocateArray_overflow_run target _ heap (intDimensionsFit dims) hprod]
      simp only [hprod, ite_false, Except.bind]

abbrev sizedLengthCollect {Tag α X Z : Type} (length : X → Z)
    (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeLength length itr))
        (fun t _ len => arrayForLength (fun len => liftM (toInt len))
          (heapVectorAllocate (α := α)) t len) copy t itr ()) target itr

def SizedLengthCollectSpec : Prop :=
  ∀ (Tag α β X Z : Type) (values : X → List β) (length : X → Z)
    (value : Z → Int) (toInt : Z → Except Error I)
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    CollectorIntLaw value toInt → SizedCopyLaw values convert copy →
    ∀ target itr heap, value (length itr) = (values itr).length →
    (sizedLengthCollect length toInt copy target itr).run heap =
      if (values itr).length < 2 ^ 63 then
        ((values itr).mapM convert).map
          (fun converted => collectedShape target [(values itr).length] converted heap)
      else .error .inexact

theorem sizedLengthCollectSpec : SizedLengthCollectSpec := by
  intro Tag α β X Z values length value toInt convert copy hInt hcopy target itr heap hlen
  simp only [sizedLengthCollect, collectTyped, collectSized, similarShapeLength,
    vector_bind_run, vector_pure_run]
  rw [integerCollectorAllocationSpec Tag α Z value toInt hInt]
  by_cases hn : (values itr).length < 2 ^ 63
  · have hfit : IntTy.i64.min ≤ value (length itr) ∧
        value (length itr) ≤ IntTy.i64.max := by
      rw [hlen]
      change -9223372036854775808 ≤ ((values itr).length : Int) ∧
        ((values itr).length : Int) ≤ 9223372036854775807
      change (values itr).length < 9223372036854775808 at hn
      omega
    have hnegative : ¬ value (length itr) < 0 := by rw [hlen]; omega
    simp only [hfit, and_self, ite_true, hnegative, ite_false, freshVectorAllocation]
    simp only [hlen, Int.toNat_natCast, hn, ite_true]
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.mul_one]
      using sizedCopy_fresh values convert copy hcopy target [(values itr).length]
        itr heap (by simp) (by simpa using hn)
  · have hfit : ¬ (IntTy.i64.min ≤ value (length itr) ∧
        value (length itr) ≤ IntTy.i64.max) := by
      rw [hlen]
      change ¬ (-9223372036854775808 ≤ ((values itr).length : Int) ∧
        ((values itr).length : Int) ≤ 9223372036854775807)
      change ¬ (values itr).length < 9223372036854775808 at hn
      omega
    simp only [hfit, ite_false, hn]

abbrev shapedCollectorAllocate {Tag α Axes : Type}
    (toShape : Axes → VectorM α (List I)) (target : Tag) (axes : Axes) :
    VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.similarStorageOneTo toShape
    (fun ty dims => JuliaLean.base.abstractarray.similarStorageDims
      (fun _ dims => heapAllocateIntDims target dims) ty dims)
    (HeapArray Tag) axes

abbrev sizedShapeCollect {Tag α X Axes : Type} (axes : X → Axes)
    (toShape : Axes → VectorM α (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
        (fun t _ axs => arrayForShape (shapedCollectorAllocate toShape) t axs)
        copy t itr ()) target itr

theorem shapedCollectorAllocate_run {Tag α Axes : Type}
    (toShape : Axes → VectorM α (List I)) (shapePolicy : Axes → Except Error (List I))
    (hlaw : ∀ axes heap, (toShape axes).run heap =
      (shapePolicy axes).map (fun dims => (dims, heap)))
    (target : Tag) (axes : Axes) (heap : VectorHeap α) :
    (shapedCollectorAllocate toShape target axes).run heap =
      ((shapePolicy axes).bind intDimensionShape).bind
        (fun shape => freshShapeAllocation target shape heap) := by
  simp only [shapedCollectorAllocate, JuliaLean.base.abstractarray.similarStorageOneTo,
    JuliaLean.base.abstractarray.similarStorageDims, vector_bind_run, hlaw]
  cases h : shapePolicy axes with
  | error error => simp only [Except.map, Except.bind]
  | ok dims => simp only [Except.map, Except.bind, heapAllocateIntDims_run]

def SizedShapeCollectSpec : Prop :=
  ∀ (Tag α β X Axes : Type) (values : X → List β) (axes : X → Axes)
    (toShape : Axes → VectorM α (List I)) (shapePolicy : Axes → Except Error (List I))
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    (∀ axs heap, (toShape axs).run heap =
      (shapePolicy axs).map (fun dims => (dims, heap))) →
    SizedCopyLaw values convert copy →
    ∀ target itr heap,
    (∀ dims shape, shapePolicy (axes itr) = .ok dims →
      intDimensionShape dims = .ok shape → shape.prod = (values itr).length) →
    (sizedShapeCollect axes toShape copy target itr).run heap =
      ((shapePolicy (axes itr)).bind intDimensionShape).bind
        (fun shape => ((values itr).mapM convert).map
          (fun converted => collectedShape target shape converted heap))

theorem sizedShapeCollectSpec : SizedShapeCollectSpec := by
  intro Tag α β X Axes values axes toShape shapePolicy convert copy hlaw hcopy
    target itr heap hlen
  simp only [sizedShapeCollect, collectTyped, collectSized, similarShapeAxes, arrayForShape,
    vector_bind_run, vector_pure_run]
  rw [shapedCollectorAllocate_run toShape shapePolicy hlaw]
  cases hp : shapePolicy (axes itr) with
  | error error => simp only [Except.bind]
  | ok dims =>
    simp only [Except.bind]
    cases hd : intDimensionShape dims with
    | error error => rfl
    | ok shape =>
      simp only [freshShapeAllocation]
      exact sizedCopy_fresh values convert copy hcopy target shape itr heap
        (hlen dims shape hp hd) (intDimensionShape_bound dims shape hd)

def SizedIntegerLengthSpec : Prop :=
  ∀ (Tag X : Type) (T S L : IntTy) (values : X → List (JInt S))
    (length : X → JInt L)
    (copy : HeapArray Tag → X → VectorM (JInt T) (HeapArray Tag)),
    SizedCopyLaw values
      (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)) copy →
    ∀ target itr heap, (length itr).val = (values itr).length →
    (sizedLengthCollect length
      (fun x => (JuliaLean.base.int.convert .i64 x).mapError (fun _ => Error.inexact))
      copy target itr).run heap =
      if (values itr).length < 2 ^ 63 then
        if ∀ x ∈ values itr, T.min ≤ x.val ∧ x.val ≤ T.max then
          .ok (collectedShape target [(values itr).length]
            ((values itr).map (fun x => JInt.wrap T x.val)) heap)
        else .error .inexact
      else .error .inexact

theorem sizedIntegerLengthSpec : SizedIntegerLengthSpec := by
  intro Tag X T S L values length copy hcopy target itr heap hlen
  have hInt : CollectorIntLaw Subtype.val
      (fun x : JInt L =>
        (JuliaLean.base.int.convert .i64 x).mapError (fun _ => Error.inexact)) :=
    fun x => bitinteger_array_conversion .i64 x
  rw [sizedLengthCollectSpec Tag (JInt T) (JInt S) X (JInt L) values length
    Subtype.val _ _ copy hInt hcopy target itr heap hlen]
  by_cases hn : (values itr).length < 2 ^ 63
  · simp only [hn, ite_true]
    by_cases hfit : ∀ x ∈ values itr, T.min ≤ x.val ∧ x.val ≤ T.max
    · rw [bitinteger_array_mapM_success T (values itr) hfit]
      simp only [ite_eq_left hfit, Except.map]
    · have hbad : ∃ x ∈ values itr, ¬(T.min ≤ x.val ∧ x.val ≤ T.max) := by
        simpa only [Classical.not_forall, exists_prop] using hfit
      rw [bitinteger_array_mapM_failure T (values itr) hbad]
      simp only [ite_eq_right hfit, Except.map]
  · simp only [hn, ite_false]

def SizedIntegerShapeSpec : Prop :=
  ∀ (Tag X Axes : Type) (T S : IntTy) (values : X → List (JInt S))
    (axes : X → Axes) (toShape : Axes → VectorM (JInt T) (List I))
    (shapePolicy : Axes → Except Error (List I))
    (copy : HeapArray Tag → X → VectorM (JInt T) (HeapArray Tag)),
    (∀ axs heap, (toShape axs).run heap =
      (shapePolicy axs).map (fun dims => (dims, heap))) →
    SizedCopyLaw values
      (fun x => (JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)) copy →
    ∀ target itr heap,
    (∀ dims shape, shapePolicy (axes itr) = .ok dims →
      intDimensionShape dims = .ok shape → shape.prod = (values itr).length) →
    (sizedShapeCollect axes toShape copy target itr).run heap =
      ((shapePolicy (axes itr)).bind intDimensionShape).bind
        (fun shape =>
          if ∀ x ∈ values itr, T.min ≤ x.val ∧ x.val ≤ T.max then
            .ok (collectedShape target shape
              ((values itr).map (fun x => JInt.wrap T x.val)) heap)
          else .error .inexact)

theorem sizedIntegerShapeSpec : SizedIntegerShapeSpec := by
  intro Tag X Axes T S values axes toShape shapePolicy copy hlaw hcopy target itr heap hlen
  rw [sizedShapeCollectSpec Tag (JInt T) (JInt S) X Axes values axes toShape shapePolicy
    _ copy hlaw hcopy target itr heap hlen]
  by_cases hfit : ∀ x ∈ values itr, T.min ≤ x.val ∧ x.val ≤ T.max
  · rw [bitinteger_array_mapM_success T (values itr) hfit]
    simp only [ite_eq_left hfit, Except.map]
  · have hbad : ∃ x ∈ values itr, ¬(T.min ≤ x.val ∧ x.val ≤ T.max) := by
      simpa only [Classical.not_forall, exists_prop] using hfit
    rw [bitinteger_array_mapM_failure T (values itr) hbad]
    simp only [ite_eq_right hfit, Except.map]

theorem heapNatDimension_value (dims : List Nat) (hfit : heapDimensionsFit dims = true)
    (n : Nat) (hn : n ∈ dims) : (JInt.wrap .i64 (n : Int)).val = n := by
  have hb := List.all_eq_true.mp hfit n hn
  exact collectorLengthFits n (of_decide_eq_true hb)

theorem heapNatDimension_toNat (dims : List Nat) (hfit : heapDimensionsFit dims = true)
    (n : Nat) (hn : n ∈ dims) : (JInt.wrap .i64 (n : Int)).val.toNat = n :=
  (congrArg Int.toNat (heapNatDimension_value dims hfit n hn)).trans (Int.toNat_natCast n)

theorem heapNatDimensions_values (dims : List Nat) (hfit : heapDimensionsFit dims = true) :
    (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int))).map
      (fun n => n.val.toNat) = dims := by
  revert hfit
  induction dims with
  | nil => intro _; rfl
  | cons n ns ih =>
    intro hfit
    have htail : heapDimensionsFit ns = true := by
      apply List.all_eq_true.mpr
      intro value hvalue
      exact List.all_eq_true.mp hfit value (List.mem_cons_of_mem n hvalue)
    exact List.cons_eq_cons.mpr
      ⟨heapNatDimension_toNat (n :: ns) hfit n (by simp), ih htail⟩

theorem heapNatDimensions_nonnegative (dims : List Nat)
    (hfit : heapDimensionsFit dims = true) :
    (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int))).any
      (fun n => decide (n.val < 0)) = false := by
  apply List.any_eq_false.mpr
  intro n hn
  obtain ⟨value, hv, rfl⟩ := List.mem_map.mp hn
  have hnonnegative : 0 ≤ (JInt.wrap .i64 (value : Int)).val :=
    Int.le_trans (Int.natCast_nonneg value)
      (Int.le_of_eq (heapNatDimension_value dims hfit value hv).symm)
  simpa only [decide_eq_true_eq] using Int.not_lt.mpr hnonnegative

theorem heapAllocateIntDims_nat_run {Tag α : Type} (target : Tag) (dims : List Nat)
    (heap : VectorHeap α) (hfit : heapDimensionsFit dims = true)
    (hprod : dims.prod < 2 ^ 63) :
    (heapAllocateIntDims target (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int)))).run heap =
      freshShapeAllocation target dims heap := by
  have hmap := heapNatDimensions_values dims hfit
  have hnegative := heapNatDimensions_nonnegative dims hfit
  have hproduct : ((dims.map (fun n : Nat => JInt.wrap .i64 (n : Int))).map
      (fun n => n.val.toNat)).prod < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.le_of_eq (congrArg List.prod hmap)) hprod
  simp only [heapAllocateIntDims, hnegative, Bool.false_eq_true, ite_false]
  rw [heapAllocateArray_run target _ heap (intDimensionsFit _) hproduct]
  simp only [freshShapeAllocation, hmap]

def NativeHeapShapeCollectSpec : Prop :=
  ∀ (Tag α Axes : Type) (axes : HeapArray Tag → Axes)
    (toShape : Axes → VectorM α (List I))
    (convert : Option α → Except Error (Option α)),
    (∀ src heap, heapDimensionsFit src.dimensions = true →
      (toShape (axes src)).run heap =
        .ok (src.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int)), heap)) →
    ∀ target heap src xs, heap[src.handle]? = some xs →
    src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    (sizedShapeCollect axes toShape (heapArrayCopy convert) target src).run heap =
      (xs.mapM convert).map (fun values =>
        (HeapArray.mk heap.length target src.dimensions
          (src.dimensions.map (fun n => (1, n))), heap ++ [values]))

theorem nativeHeapShapeCollectSpec : NativeHeapShapeCollectSpec := by
  intro Tag α Axes axes toShape convert hshape target heap src xs hs hl hn hfit
  have hsrcLt : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  let fresh : HeapArray Tag :=
    ⟨heap.length, target, src.dimensions, src.dimensions.map (fun n => (1, n))⟩
  let allocated := heap ++ [List.replicate src.dimensions.prod (none : Option α)]
  have hsrc : allocated[src.handle]? = some xs := by
    simpa only [allocated, List.getElem?_append_left hsrcLt] using hs
  have hdest : allocated[fresh.handle]? =
      some (List.replicate src.dimensions.prod none) := by
    simp [allocated, fresh]
  simp only [sizedShapeCollect, collectTyped, collectSized, similarShapeAxes, arrayForShape,
    shapedCollectorAllocate, JuliaLean.base.abstractarray.similarStorageOneTo,
    JuliaLean.base.abstractarray.similarStorageDims, vector_bind_run, vector_pure_run]
  rw [hshape src heap hfit]
  simp only
  rw [heapAllocateIntDims_nat_run target src.dimensions heap hfit (by omega)]
  simp only [freshShapeAllocation]
  change (heapArrayCopy convert fresh src).run allocated = _
  rw [heapArrayCopy_run convert allocated fresh src xs
    (List.replicate src.dimensions.prod none) hsrc hdest (by simp [hl]) hn]
  by_cases hempty : xs = []
  · have hz : src.dimensions.prod = 0 := by simpa only [hempty, List.length_nil] using hl
    simp only [hempty, ite_true, List.mapM_nil, Except.map]
    simp only [allocated, fresh, hz, List.replicate_zero] <;> rfl
  · simp only [hempty, ite_false]
    cases h : xs.mapM convert <;> simp [allocated, fresh, List.set_append_right]

def NativeIntegerHeapShapeSpec : Prop :=
  ∀ (Axes : Type) (T S : IntTy) (axes : HeapArray IntTy → Axes)
    (toShape : Axes → VectorM (Sum (JInt T) (JInt S)) (List I))
    (slotConvert : Option (Sum (JInt T) (JInt S)) →
      Except Error (Option (Sum (JInt T) (JInt S)))),
    (∀ src heap, heapDimensionsFit src.dimensions = true →
      (toShape (axes src)).run heap =
        .ok (src.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int)), heap)) →
    (∀ x, slotConvert (some (.inr x)) =
      ((JuliaLean.base.int.convert T x).mapError (fun _ => Error.inexact)).map
        (fun y => some (.inl y))) →
    ∀ (heap : VectorHeap (Sum (JInt T) (JInt S))) (src : HeapArray IntTy)
      (xs : List (JInt S)), heap[src.handle]? = some (xs.map (fun x => some (.inr x))) →
    src.elementType = S → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    (sizedShapeCollect axes toShape (heapArrayCopy slotConvert) T src).run heap =
      if ∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max then
        .ok (HeapArray.mk heap.length T src.dimensions
          (src.dimensions.map (fun n => (1, n))),
          heap ++ [xs.map (fun x => some (.inl (JInt.wrap T x.val)))])
      else .error .inexact

theorem nativeIntegerHeapShapeSpec : NativeIntegerHeapShapeSpec := by
  intro Axes T S axes toShape slotConvert hshape hslot heap src xs hs htype hl hn hfit
  have h := nativeHeapShapeCollectSpec IntTy (Sum (JInt T) (JInt S)) Axes
    axes toShape slotConvert hshape T heap src (xs.map (fun x => some (.inr x)))
    hs (by simpa only [List.length_map] using hl)
    (by simpa only [List.length_map] using hn) hfit
  rw [typed_slot_mapM _ slotConvert hslot xs] at h
  by_cases hvalues : ∀ x ∈ xs, T.min ≤ x.val ∧ x.val ≤ T.max
  · rw [ite_eq_left hvalues]
    simpa only [bitinteger_array_mapM_success T xs hvalues, Except.map,
      List.map_map, Function.comp_def] using h
  · have hbad : ∃ x ∈ xs, ¬(T.min ≤ x.val ∧ x.val ≤ T.max) := by
      simpa only [Classical.not_forall, exists_prop] using hvalues
    rw [ite_eq_right hvalues]
    simpa only [bitinteger_array_mapM_failure T xs hbad, Except.map] using h

abbrev genericSizedShapeCollect {Tag α X Axes : Type} (axes : X → Axes)
    (similar : Tag → Axes → VectorM α (HeapArray Tag))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (target : Tag) (itr : X) : VectorM α (HeapArray Tag) :=
  collectTyped (fun _ => ())
    (fun t itr (_ : Unit) =>
      collectSized (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
        (fun t _ axs => arrayForShape similar t axs) copy t itr ()) target itr

def GeneralSizedShapeSpec : Prop :=
  ∀ (Tag α β X Axes : Type) (values : X → List β) (axes : X → Axes)
    (similar : Tag → Axes → VectorM α (HeapArray Tag))
    (policy : Axes → Except Error (List Nat))
    (convert : β → Except Error α)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    (∀ target axs heap, (similar target axs).run heap =
      (policy axs).bind (fun shape => freshShapeAllocation target shape heap)) →
    SizedCopyLaw values convert copy →
    (∀ axs shape, policy axs = .ok shape → shape.prod < 2 ^ 63) →
    ∀ target itr heap,
    (∀ shape, policy (axes itr) = .ok shape → shape.prod = (values itr).length) →
    (genericSizedShapeCollect axes similar copy target itr).run heap =
      (policy (axes itr)).bind (fun shape => ((values itr).mapM convert).map
        (fun converted => collectedShape target shape converted heap))

theorem generalSizedShapeSpec : GeneralSizedShapeSpec := by
  intro Tag α β X Axes values axes similar policy convert copy hsimilar hcopy hbound
    target itr heap hlen
  simp only [genericSizedShapeCollect, collectTyped, collectSized, similarShapeAxes,
    arrayForShape, vector_bind_run, vector_pure_run]
  rw [hsimilar target (axes itr) heap]
  cases hp : policy (axes itr) with
  | error error => rfl
  | ok shape =>
    simp only [Except.bind, freshShapeAllocation]
    exact sizedCopy_fresh values convert copy hcopy target shape itr heap
      (hlen shape hp) (hbound (axes itr) shape hp)

def CompleteTypedCollectSpec : Prop :=
  CompleteUnknownCollectionSpec ∧ SizedLengthCollectSpec ∧ SizedShapeCollectSpec ∧
    SizedIntegerLengthSpec ∧ SizedIntegerShapeSpec ∧
    NativeHeapShapeCollectSpec ∧ NativeIntegerHeapShapeSpec ∧ GeneralSizedShapeSpec

theorem completeTypedCollectSpec : CompleteTypedCollectSpec :=
  ⟨completeUnknownCollectionSpec, sizedLengthCollectSpec, sizedShapeCollectSpec,
    sizedIntegerLengthSpec, sizedIntegerShapeSpec,
    nativeHeapShapeCollectSpec, nativeIntegerHeapShapeSpec, generalSizedShapeSpec⟩

theorem heapAllocateIntDims_singleton {Tag α : Type} (target : Tag) (n : I) :
    heapAllocateIntDims (α := α) target [n] = heapVectorAllocate target n := by
  funext heap
  by_cases hn : n.val < 0
  · simp only [heapAllocateIntDims, heapVectorAllocate, List.any_cons, List.any_nil,
      Bool.or_false, decide_eq_true_eq, hn, ite_true] <;> rfl
  · simp only [heapAllocateIntDims, heapVectorAllocate, List.any_cons, List.any_nil,
      Bool.or_false, decide_eq_true_eq, hn, ite_false, List.map_cons, List.map_nil]

abbrev nativeLengthSimilar {C Tag α Z : Type} (toInt : Z → Except Error I)
    (c : C) (target : Tag) (n : Z) : VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.similarTypeVarargs
    (fun c t dims =>
      JuliaLean.base.abstractarray.similarOneTo
        (JuliaLean.base.abstractarray.toShapeMixed
          (JuliaLean.base.abstractarray.toShapeInteger (fun n => liftM (toInt n))))
        (fun c (_ : Type) dims => similar419 (heapAllocateIntDims t) c dims)
        c α dims) c target [n]

theorem nativeLengthSimilar_eq {C Tag α Z : Type} (toInt : Z → Except Error I)
    (c : C) (target : Tag) (n : Z) :
    nativeLengthSimilar (α := α) toInt c target n =
      arrayForLength (fun n => liftM (toInt n)) heapVectorAllocate target n := by
  funext heap
  change (nativeLengthSimilar (α := α) toInt c target n).run heap =
    (arrayForLength (fun n => liftM (toInt n)) heapVectorAllocate target n).run heap
  simp only [nativeLengthSimilar, JuliaLean.base.abstractarray.similarTypeVarargs,
    JuliaLean.base.abstractarray.similarOneTo, JuliaLean.base.abstractarray.toShapeMixed,
    JuliaLean.base.abstractarray.toShapeInteger, similar419, arrayForLength,
    List.mapM_cons, List.mapM_nil, vector_bind_run, vector_lift_run, vector_pure_run]
  cases h : toInt n with
  | error error => rfl
  | ok value =>
    simp only [Except.map]
    rw [heapAllocateIntDims_singleton]

abbrev nativeAxesSimilar {C Tag α Axes : Type}
    (toShape : Axes → VectorM α (List I)) (c : C) (target : Tag) (axes : Axes) :
    VectorM α (HeapArray Tag) :=
  JuliaLean.base.abstractarray.similarOneTo toShape
    (fun c (_ : Type) dims => similar419 (heapAllocateIntDims target) c dims) c α axes

theorem nativeAxesSimilar_eq {C Tag α Axes : Type}
    (toShape : Axes → VectorM α (List I)) (c : C) (target : Tag) (axes : Axes) :
    nativeAxesSimilar toShape c target axes = shapedCollectorAllocate toShape target axes := rfl

def IteratorAllocatorRoutesSpec : Prop :=
  (∀ (Tag α X : Type) (target : Tag) (itr : X) (heap : VectorHeap α),
    (arrayFor (fun itr (_ : Unit) => pure (similarShapeUnknown itr))
      (fun t _ _ => arrayForUnknown (heapVectorAllocate (α := α)) t)
      target itr ()).run heap = freshVectorAllocation target 0 heap) ∧
  (∀ (Tag α X Z : Type) (length : X → Z) (value : Z → Int)
    (toInt : Z → Except Error I), CollectorIntLaw value toInt →
    ∀ (target : Tag) (itr : X) (heap : VectorHeap α),
    (arrayFor (fun itr (_ : Unit) => pure (similarShapeLength length itr))
      (fun t _ n => arrayForLength (fun n => liftM (toInt n)) heapVectorAllocate t n)
      target itr ()).run heap =
      if IntTy.i64.min ≤ value (length itr) ∧ value (length itr) ≤ IntTy.i64.max then
        if value (length itr) < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target (value (length itr)).toNat heap
      else .error .inexact) ∧
  (∀ (Tag α X Axes : Type) (axes : X → Axes)
    (toShape : Axes → VectorM α (List I)) (policy : Axes → Except Error (List I)),
    (∀ axs heap, (toShape axs).run heap = (policy axs).map (fun dims => (dims, heap))) →
    ∀ (target : Tag) (itr : X) (heap : VectorHeap α),
    (arrayFor (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
      (fun t _ axs => arrayForShape (shapedCollectorAllocate toShape) t axs)
      target itr ()).run heap =
      ((policy (axes itr)).bind intDimensionShape).bind
        (fun shape => freshShapeAllocation target shape heap))

theorem iteratorAllocatorRoutesSpec : IteratorAllocatorRoutesSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro Tag α X target itr heap
    simp only [arrayFor, arrayForUnknown, vector_bind_run, vector_pure_run]
    exact emptyCollectorAllocationSpec Tag α target heap
  · intro Tag α X Z length value toInt hlaw target itr heap
    simp only [arrayFor, similarShapeLength, vector_bind_run, vector_pure_run]
    exact integerCollectorAllocationSpec Tag α Z value toInt hlaw target (length itr) heap
  · intro Tag α X Axes axes toShape policy hlaw target itr heap
    simp only [arrayFor, similarShapeAxes, arrayForShape, vector_bind_run, vector_pure_run]
    exact shapedCollectorAllocate_run toShape policy hlaw target (axes itr) heap

def SimilarIteratorAllocatorsSpec : Prop :=
  (∀ (C Tag α X Z : Type) (value : Z → Int) (toInt : Z → Except Error I),
    CollectorIntLaw value toInt → ∀ (c : C) (target : Tag) (itr : X) n (heap : VectorHeap α),
    (similarForLength (nativeLengthSimilar toInt) c target itr n).run heap =
      if IntTy.i64.min ≤ value n ∧ value n ≤ IntTy.i64.max then
        if value n < 0 then .error (.argument "invalid Array dimensions")
        else freshVectorAllocation target (value n).toNat heap
      else .error .inexact) ∧
  (∀ (C Tag α X Axes : Type) (toShape : Axes → VectorM α (List I))
    (policy : Axes → Except Error (List I)),
    (∀ axs heap, (toShape axs).run heap = (policy axs).map (fun dims => (dims, heap))) →
    ∀ (c : C) (target : Tag) (itr : X) axs heap,
    (similarForAxes (nativeAxesSimilar toShape) c target itr axs).run heap =
      ((policy axs).bind intDimensionShape).bind
        (fun shape => freshShapeAllocation target shape heap)) ∧
  (∀ (C Tag α X Size Shape : Type) (size : C → List Nat)
    (similar : C → Tag → VectorM α (HeapArray Tag)),
    (∀ c target heap, (similar c target).run heap = freshShapeAllocation target (size c) heap) →
    ∀ c target (itr : X) (isz : Size) (shape : Shape) heap,
    (similarForGeneric similar c target itr isz shape).run heap =
      freshShapeAllocation target (size c) heap)

theorem similarIteratorAllocatorsSpec : SimilarIteratorAllocatorsSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro C Tag α X Z value toInt hlaw c target itr n heap
    simp only [similarForLength, nativeLengthSimilar_eq]
    exact integerCollectorAllocationSpec Tag α Z value toInt hlaw target n heap
  · intro C Tag α X Axes toShape policy hlaw c target itr axs heap
    simp only [similarForAxes, nativeAxesSimilar_eq]
    exact shapedCollectorAllocate_run toShape policy hlaw target axs heap
  · intro C Tag α X Size Shape size similar hlaw c target itr isz shape heap
    exact hlaw c target heap

def CompleteIteratorAllocatorsSpec : Prop :=
  CompleteCollectorAllocationSpec ∧ CompleteUnknownSimilarSpec ∧
    IteratorAllocatorRoutesSpec ∧ SimilarIteratorAllocatorsSpec

theorem completeIteratorAllocatorsSpec : CompleteIteratorAllocatorsSpec :=
  ⟨completeCollectorAllocationSpec, completeUnknownSimilarSpec,
    iteratorAllocatorRoutesSpec, similarIteratorAllocatorsSpec⟩

/-- Reading an AbstractArray element is undefined exactly at an unassigned slot. -/
def collectReadSlot : Option α → Except Error (Option α)
  | none => .error .undefinedReference
  | some x => .ok (some x)

theorem collectReadSlot_map (xs : List α) :
    (xs.map some).mapM collectReadSlot = .ok (xs.map some) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, collectReadSlot, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem collectReadSlot_undefined (xs : List (Option α)) (h : none ∈ xs) :
    xs.mapM collectReadSlot = .error .undefinedReference := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases x with
    | none => rfl
    | some x =>
      have ht : none ∈ xs := by simpa using h
      simp [List.mapM_cons, collectReadSlot, ih ht, Bind.bind, Except.bind]

/-- The external unaliased-copy interface reads source elements in linear order,
retains the allocated header, and changes only the destination's slots. -/
def CollectUnaliasedLaw {Tag α Style : Type}
    (destStyle srcStyle : HeapArray Tag → Style)
    (copy : Style → HeapArray Tag → Style → HeapArray Tag → VectorM α (HeapArray Tag)) : Prop :=
  ∀ heap dest src xs ys, heap[src.handle]? = some xs → heap[dest.handle]? = some ys →
    dest.elementType = src.elementType → dest.dimensions.prod = xs.length →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    (copy (destStyle dest) dest (srcStyle src) src).run heap =
      (xs.mapM collectReadSlot).map (fun values => (dest, heap.set dest.handle values))

/-- The Cartesian-copy interface pairs the destination's one-based Cartesian
indices with the source's original axes, in the same linear order. -/
def CollectCartesianLaw {Tag α Indices : Type}
    (cartesian : List (Int × Nat) → Indices)
    (copy : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag)) : Prop :=
  ∀ heap dest src xs ys, heap[src.handle]? = some xs → heap[dest.handle]? = some ys →
    dest.elementType = src.elementType → dest.dimensions.prod = xs.length →
    ys.length = xs.length → xs.length < 2 ^ 63 →
    (copy dest (cartesian dest.axes) src (cartesian src.axes)).run heap =
      (xs.mapM collectReadSlot).map (fun values => (dest, heap.set dest.handle values))

abbrev collectHeapEmpty {Tag α : Type} (a : HeapArray Tag) : VectorM α Bool := do
  let xs ← heapSlots a.handle
  pure xs.isEmpty

theorem collectHeapEmpty_run {Tag α : Type} (heap : VectorHeap α) (src : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[src.handle]? = some xs) :
    (collectHeapEmpty src).run heap = .ok (xs.isEmpty, heap) := by
  simp only [collectHeapEmpty, vector_bind_run, heapSlots_run, hs, vector_pure_run]

/-- Trusted Julia dispatch selects the empty-tuple, OneTo-tuple, or general
axes method; all three implementations below are the source-mirrored methods. -/
abbrev collectHeapIndices {Tag α Style Indices : Type}
    (destStyle srcStyle : HeapArray Tag → Style)
    (unaliased : Style → HeapArray Tag → Style → HeapArray Tag →
      VectorM α (HeapArray Tag))
    (cartesian : List (Int × Nat) → Indices)
    (indexed : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag))
    (axes : List (Int × Nat)) (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  if axes = [] then
    collectIndicesZero (fun a => heapAllocateArray a.elementType []) collectHeapEmpty
      destStyle srcStyle unaliased src
  else if axes.all (fun ax => decide (ax.1 = 1)) then
    collectIndicesOneTo (fun ax => JInt.wrap .i64 (ax.2 : Int))
      (fun a dims => heapAllocateIntDims a.elementType dims)
      collectHeapEmpty destStyle srcStyle unaliased axes src
  else
    collectIndicesGeneric (fun ax => JInt.wrap .i64 (ax.2 : Int))
      (fun a dims => heapAllocateIntDims a.elementType dims)
      HeapArray.axes cartesian indexed axes axes src

theorem collectHeapIndices_spec {Tag α Style Indices : Type}
    (destStyle srcStyle : HeapArray Tag → Style)
    (unaliased : Style → HeapArray Tag → Style → HeapArray Tag →
      VectorM α (HeapArray Tag))
    (cartesian : List (Int × Nat) → Indices)
    (indexed : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag))
    (hu : CollectUnaliasedLaw destStyle srcStyle unaliased)
    (hi : CollectCartesianLaw cartesian indexed)
    (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (hs : heap[src.handle]? = some xs) (hd : src.dimensions = src.axes.map Prod.snd)
    (hl : src.dimensions.prod = xs.length) (hn : xs.length < 2 ^ 63)
    (hfit : heapDimensionsFit src.dimensions = true) :
    (collectHeapIndices destStyle srcStyle unaliased cartesian indexed src.axes src).run heap =
      (xs.mapM collectReadSlot).map (fun values =>
        (HeapArray.mk heap.length src.elementType src.dimensions
          (src.dimensions.map (fun n => (1, n))), heap ++ [values])) := by
  have hslt : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  let fresh : HeapArray Tag :=
    ⟨heap.length, src.elementType, src.dimensions, src.dimensions.map (fun n => (1, n))⟩
  let allocated := heap ++ [List.replicate src.dimensions.prod (none : Option α)]
  have hsrc : allocated[src.handle]? = some xs := by
    simpa only [allocated, List.getElem?_append_left hslt] using hs
  have hdest : allocated[fresh.handle]? =
      some (List.replicate src.dimensions.prod none) := by simp [allocated, fresh]
  have hcopyU :
      (unaliased (destStyle fresh) fresh (srcStyle src) src).run allocated =
        (xs.mapM collectReadSlot).map (fun values => (fresh, heap ++ [values])) := by
    rw [hu allocated fresh src xs _ hsrc hdest rfl hl (by simp [hl]) hn]
    cases hx : xs.mapM collectReadSlot <;> simp [allocated, fresh, List.set_append_right]
  have hcopyI :
      (indexed fresh (cartesian fresh.axes) src (cartesian src.axes)).run allocated =
        (xs.mapM collectReadSlot).map (fun values => (fresh, heap ++ [values])) := by
    rw [hi allocated fresh src xs _ hsrc hdest rfl hl (by simp [hl]) hn]
    cases hx : xs.mapM collectReadSlot <;> simp [allocated, fresh, List.set_append_right]
  have hempty :
      (if xs.isEmpty then .ok (fresh, allocated) else
        (unaliased (destStyle fresh) fresh (srcStyle src) src).run allocated) =
      (xs.mapM collectReadSlot).map (fun values => (fresh, heap ++ [values])) := by
    cases xs with
    | nil =>
      have hz : src.dimensions.prod = 0 := hl
      simp [allocated, hz, Except.map, Pure.pure, Except.pure]
    | cons x xs => simpa using hcopyU
  unfold collectHeapIndices
  by_cases hz : src.axes = []
  · have hdz : src.dimensions = [] := by simpa [hz] using hd
    simp only [hz, ite_true, collectIndicesZero, vector_bind_run]
    rw [← hdz, heapAllocateArray_run src.elementType src.dimensions heap hfit (by omega)]
    simp only [heapSlots_run, List.getElem?_append_left hslt, hs, vector_ite_run, vector_pure_run]
    exact hempty
  · simp only [hz, ite_false]
    split
    · simp only [collectIndicesOneTo, vector_bind_run]
      have hdims : src.axes.map (fun ax => JInt.wrap .i64 (ax.2 : Int)) =
          src.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int)) := by
        rw [hd, List.map_map]
        rfl
      rw [hdims, heapAllocateIntDims_nat_run src.elementType src.dimensions heap hfit (by omega)]
      simp only [freshShapeAllocation, heapSlots_run, List.getElem?_append_left hslt,
        hs, vector_ite_run, vector_pure_run]
      exact hempty
    · simp only [collectIndicesGeneric, vector_bind_run]
      have hdims : src.axes.map (fun ax => JInt.wrap .i64 (ax.2 : Int)) =
          src.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int)) := by
        rw [hd, List.map_map]
        rfl
      rw [hdims, heapAllocateIntDims_nat_run src.elementType src.dimensions heap hfit (by omega)]
      simp only [freshShapeAllocation]
      exact hcopyI

/-- Array collection preserves type, shape and linear order, normalizes axes,
allocates distinct storage without changing old arrays, and rejects unassigned
source elements. The two copy operations are the external AbstractArray interfaces. -/
def ArrayCollectionSpec : Prop :=
  ∀ (Tag α Style Indices : Type)
    (destStyle srcStyle : HeapArray Tag → Style)
    (unaliased : Style → HeapArray Tag → Style → HeapArray Tag →
      VectorM α (HeapArray Tag))
    (cartesian : List (Int × Nat) → Indices)
    (indexed : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag)),
    CollectUnaliasedLaw destStyle srcStyle unaliased →
    CollectCartesianLaw cartesian indexed →
    ∀ (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions = src.axes.map Prod.snd →
    src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    heapDimensionsFit src.dimensions = true →
    let operation := collectArray HeapArray.axes
      (collectHeapIndices destStyle srcStyle unaliased cartesian indexed) src
    (operation.run heap =
      (xs.mapM collectReadSlot).map (fun values =>
        (HeapArray.mk heap.length src.elementType src.dimensions
          (src.dimensions.map (fun n => (1, n))), heap ++ [values]))) ∧
    (∀ values : List α, xs = values.map some → operation.run heap =
      .ok (HeapArray.mk heap.length src.elementType src.dimensions
        (src.dimensions.map (fun n => (1, n))), heap ++ [xs])) ∧
    (none ∈ xs → operation.run heap = .error .undefinedReference)

theorem arrayCollectionSpec : ArrayCollectionSpec := by
  intro Tag α Style Indices destStyle srcStyle unaliased cartesian indexed hu hi
    heap src xs hs hd hl hn hfit operation
  have h := collectHeapIndices_spec destStyle srcStyle unaliased cartesian indexed
    hu hi heap src xs hs hd hl hn hfit
  change operation.run heap = _ at h
  refine ⟨h, ?_, ?_⟩
  · intro values hv
    rw [h, hv, collectReadSlot_map]
    rfl
  · intro hu
    rw [h, collectReadSlot_undefined xs hu]
    rfl

/-- The inferred default type is an upper bound on every yielded value's type.
This only assumes the external inference and type-union operations' documented
upper-bound laws, including the special constructor-Generator inference path. -/
def DefaultEltypeBoundSpec : Prop :=
  ∀ (X T α : Type) (values : X → List α) (typeof : α → T)
    (sub : T → T → Prop)
    (isGenerator functionIsType : X → Bool)
    (functionType inferredType : X → T) (promote : T → T),
    (∀ a b c, sub a b → sub b c → sub a c) →
    (∀ t, sub t (promote t)) →
    (∀ itr x, x ∈ values itr → sub (typeof x) (inferredType itr)) →
    (∀ itr, isGenerator itr = true → functionIsType itr = true →
      ∀ x ∈ values itr, sub (typeof x) (functionType itr)) →
    ∀ itr x, x ∈ values itr →
      sub (typeof x) (defaultEltype isGenerator functionIsType functionType inferredType promote itr)

theorem defaultEltypeBoundSpec : DefaultEltypeBoundSpec := by
  intro X T α values typeof sub gen istype ft inf promote trans hp hinf hft itr x hx
  unfold defaultEltype
  split
  · rename_i h
    have hh : gen itr = true ∧ istype itr = true := by simpa using h
    exact trans _ _ _ (hft itr hh.1 hh.2 x hx) (hp _)
  · exact trans _ _ _ (hinf itr x hx) (hp _)

abbrev knownLengthCollect {C Tag α X Z : Type} (elementType : X → Tag)
    (length : X → Z) (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (container : C) (itr : X) : VectorM α (HeapArray Tag) :=
  collectKnownSized elementType (fun itr (_ : Unit) => pure (similarShapeLength length itr))
    (fun c t itr (_ : Unit) n => similarForLength
      (fun c t n => do similar419 (heapVectorAllocate t) c (← liftM (toInt n)))
      c t itr n) copy container itr ()

def KnownLengthCollectionSpec : Prop :=
  ∀ (C Tag α X Z : Type) (elementType : X → Tag) (values : X → List α)
    (length : X → Z) (value : Z → Int) (toInt : Z → Except Error I)
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    CollectorIntLaw value toInt → SizedCopyLaw values (fun x => .ok x) copy →
    ∀ (container : C) itr heap, value (length itr) = (values itr).length →
    ∀ operation ∈ [
      knownLengthCollect elementType length toInt copy container,
      JuliaLean.base.array.collect container (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownLengthCollect elementType length toInt copy c itr),
      collectSimilar (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownLengthCollect elementType length toInt copy c itr) container],
    (operation itr).run heap =
      if (values itr).length < 2 ^ 63 then
        .ok (collectedShape (elementType itr) [(values itr).length] (values itr) heap)
      else .error .inexact

theorem knownLengthCollectionSpec : KnownLengthCollectionSpec := by
  intro C Tag α X Z elementType values length value toInt copy hInt hcopy
    container itr heap hlen operation hop
  have h := sizedLengthCollectSpec Tag α α X Z values length value toInt
    (fun x => .ok x) copy hInt hcopy (elementType itr) itr heap hlen
  have hm : (values itr).mapM (fun x => Except.ok (ε := Error) x) = .ok (values itr) := by
    induction values itr with
    | nil => rfl
    | cons x xs ih => simp [List.mapM_cons, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]
  rw [hm] at h
  have core : (knownLengthCollect elementType length toInt copy container itr).run heap =
      if (values itr).length < 2 ^ 63 then
        .ok (collectedShape (elementType itr) [(values itr).length] (values itr) heap)
      else .error .inexact := by
    simpa only [knownLengthCollect, collectKnownSized, similarForLength, similar419,
      sizedLengthCollect, collectTyped, collectSized, arrayForLength, Except.map] using h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl
  · exact core
  · exact core
  · exact core

abbrev knownShapeCollect {C Tag α X Axes : Type} (elementType : X → Tag)
    (axes : X → Axes) (toShape : Axes → VectorM α (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag))
    (container : C) (itr : X) : VectorM α (HeapArray Tag) :=
  collectKnownSized elementType (fun itr (_ : Unit) => pure (similarShapeAxes axes itr))
    (fun c t itr (_ : Unit) axs => similarForAxes
      (fun _ t axs => shapedCollectorAllocate toShape t axs) c t itr axs)
    copy container itr ()

def KnownShapeCollectionSpec : Prop :=
  ∀ (C Tag α X Axes : Type) (elementType : X → Tag) (values : X → List α)
    (axes : X → Axes) (toShape : Axes → VectorM α (List I))
    (policy : Axes → Except Error (List I))
    (copy : HeapArray Tag → X → VectorM α (HeapArray Tag)),
    (∀ axs heap, (toShape axs).run heap = (policy axs).map (fun dims => (dims, heap))) →
    SizedCopyLaw values (fun x => .ok x) copy →
    ∀ (container : C) itr heap,
    (∀ dims shape, policy (axes itr) = .ok dims →
      intDimensionShape dims = .ok shape → shape.prod = (values itr).length) →
    ∀ operation ∈ [
      knownShapeCollect elementType axes toShape copy container,
      JuliaLean.base.array.collect container (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownShapeCollect elementType axes toShape copy c itr),
      collectSimilar (fun _ : X => ()) (fun _ : X => ())
        (fun c itr (_ _ : Unit) => knownShapeCollect elementType axes toShape copy c itr) container],
    (operation itr).run heap =
      ((policy (axes itr)).bind intDimensionShape).map
        (fun shape => collectedShape (elementType itr) shape (values itr) heap)

theorem knownShapeCollectionSpec : KnownShapeCollectionSpec := by
  intro C Tag α X Axes elementType values axes toShape policy copy hlaw hcopy
    container itr heap hlen operation hop
  have h := sizedShapeCollectSpec Tag α α X Axes values axes toShape policy
    (fun x => .ok x) copy hlaw hcopy (elementType itr) itr heap hlen
  have hm : (values itr).mapM (fun x => Except.ok (ε := Error) x) = .ok (values itr) := by
    induction values itr with
    | nil => rfl
    | cons x xs ih => simp [List.mapM_cons, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]
  rw [hm] at h
  have core : (knownShapeCollect elementType axes toShape copy container itr).run heap =
      ((policy (axes itr)).bind intDimensionShape).map
        (fun shape => collectedShape (elementType itr) shape (values itr) heap) := by
    change (sizedShapeCollect axes toShape copy (elementType itr) itr).run heap = _
    rw [h]
    cases hp : ((policy (axes itr)).bind intDimensionShape) <;> rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> exact core

abbrev knownUnknownCollect {C α : Type} (container : C) (xs : List α) : MutationM α Nat :=
  collectKnownUnknown (fun _ => ())
    (fun c t => similarForUnknown
      (fun c (_ : Unit) n => similar419 (mutableAllocate 0) c n) c t xs)
    mutablePush container xs

def KnownUnknownCollectionSpec : Prop :=
  ∀ (C α : Type) (container : C) (xs : List α) (heap : MutableMemory α),
    xs.length < 2 ^ 63 →
    ∀ operation ∈ [
      knownUnknownCollect container,
      JuliaLean.base.array.collect container (fun _ : List α => ()) (fun _ : List α => ())
        (fun c itr (_ _ : Unit) => knownUnknownCollect c itr),
      collectSimilar (fun _ : List α => ()) (fun _ : List α => ())
        (fun c itr (_ _ : Unit) => knownUnknownCollect c itr) container],
    ∃ next, (operation xs).run heap = (.ok heap.arrays.length, next) ∧
      next.contents heap.arrays.length = xs.map some ∧ next.validVector heap.arrays.length

theorem knownUnknownCollectionSpec : KnownUnknownCollectionSpec := by
  intro C α container xs heap hsize operation hop
  have h := unknownTypedCollectionSpec α xs heap hsize
  have core : ∃ next, (knownUnknownCollect container xs).run heap =
      (.ok heap.arrays.length, next) ∧ next.contents heap.arrays.length = xs.map some ∧
      next.validVector heap.arrays.length := by
    simpa only [knownUnknownCollect, collectKnownUnknown, similarForUnknown, similar419,
      collectUnknown] using h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> exact core

def KnownEltypeCollectionSpec : Prop :=
  KnownLengthCollectionSpec ∧ KnownShapeCollectionSpec ∧ KnownUnknownCollectionSpec

theorem knownEltypeCollectionSpec : KnownEltypeCollectionSpec :=
  ⟨knownLengthCollectionSpec, knownShapeCollectionSpec, knownUnknownCollectionSpec⟩

/-- Cartesian assignment checks the whole index tuple, performs conversion
before bounds checking, and changes only the selected linear memory cell. -/
def CartesianAssignmentSpec : Prop :=
  ∀ (α β : Type) (slots : I → Option α)
    (bounds : List I → Bool) (linear : List I → Except Error I)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
    (v : β) (i₁ i₂ : I) (rest : List I),
    let indices := i₁ :: i₂ :: rest
    let converted := if already v then .ok (asTyped v) else convert v
    let operation := setindexCartesian already asTyped (fun x => slotLift (convert x))
      (setindexCartesianTyped
        (fun _ js => slotLift (if bounds js then .ok () else .error .bounds))
        (fun _ js => slotLift (linear js)) slotRefNew slotStore) () v i₁ i₂ rest
    (∀ e, converted = .error e → operation.run slots = (.error e, slots)) ∧
    (∀ x, converted = .ok x → bounds indices = false →
      operation.run slots = (.error .bounds, slots)) ∧
    (∀ x e, converted = .ok x → bounds indices = true → linear indices = .error e →
      operation.run slots = (.error e, slots)) ∧
    (∀ x i, converted = .ok x → bounds indices = true → linear indices = .ok i →
      operation.run slots = (.ok (), updateSlot slots i (some x)) ∧
      (updateSlot slots i (some x)) i = some x ∧
      ∀ j, j ≠ i → (updateSlot slots i (some x)) j = slots j)

theorem cartesianAssignmentSpec : CartesianAssignmentSpec := by
  intro α β slots bounds linear already asTyped convert v i₁ i₂ rest indices converted operation
  have run : operation.run slots =
      match converted with
      | .error e => (.error e, slots)
      | .ok x =>
        if bounds indices then
          match linear indices with
          | .error e => (.error e, slots)
          | .ok i => (.ok (), updateSlot slots i (some x))
        else (.error .bounds, slots) := by
    cases ha : already v <;> cases hc : convert v <;>
      cases hb : bounds indices <;> cases hl : linear indices <;>
      simp [operation, converted, indices, setindexCartesian, setindexCartesianTyped,
        slotRefNew, slotStore, slotLift, ha, hc, hb, hl,
        ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        StateT.bind, StateT.pure, Bind.bind, Pure.pure] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he; rw [run, he]
  · intro x hx hb; rw [run, hx, hb]; rfl
  · intro x e hx hb hl; rw [run, hx, hb, hl]; rfl
  · intro x i hx hb hl
    refine ⟨?_, ?_, ?_⟩
    · rw [run, hx, hb, hl]; rfl
    · simp [updateSlot]
    · intro j hj; simp [updateSlot, hj]


/-- The range's iteration values, defined without indexing arithmetic. -/
def steppedRangeValues (first step : Int) (n : Nat) : List Int :=
  (List.range n).map (fun k : Nat => first + (k : Int) * step)

abbrev scalarStepRangeGet {T S : IntTy}
    (r : JuliaLean.base.range.StepRange (JInt T) (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false)
    (fun r i => ExceptT.lift (JuliaLean.base.range._getindex_AbstractRange r i)) r i

abbrev scalarUnitRangeGet {T S : IntTy}
    (r : JuliaLean.base.range.UnitRange (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false)
    (fun r i => ExceptT.lift (JuliaLean.base.range.JGetindex.getindex r i)) r i

abbrev scalarOneToGet {T S : IntTy}
    (r : JuliaLean.base.range.OneTo (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false)
    (fun r i => ExceptT.lift (JuliaLean.base.range._getindex_AbstractRange r i)) r i

def ScalarRangeIndexSpec : Prop :=
  (∀ (R α : Type) (get : R → Bool → ExceptT Error JuliaLean.base.range.JlX α) r i,
    (getindexAbstractRange (fun _ : Bool => true) get r i).run =
      .ok (.error (.argument "invalid index of type Bool"))) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.OneTo (JInt T)) (i : JInt S),
    0 ≤ r.stop.val →
    (scalarOneToGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ r.stop.val then
        .ok (.ok (JInt.wrap T i.val))
      else .error (.jl .boundsError)) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.UnitRange (JInt T)) (i : JInt S),
    r.start.val - 1 ≤ r.stop.val →
    (scalarUnitRangeGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ r.stop.val - r.start.val + 1 then
        .ok (.ok (JInt.wrap T (r.start.val + i.val - 1)))
      else .error (.jl .boundsError)) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.StepRange (JInt T) (JInt T))
    (n : Nat) (i : JInt S),
    r.step.val ≠ 0 → r.stop.val = r.start.val + ((n : Int) - 1) * r.step.val →
    (∀ value ∈ steppedRangeValues r.start.val r.step.val n, T.min ≤ value ∧ value ≤ T.max) →
    (scalarStepRangeGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ (n : Int) then
        .ok (.ok (JInt.wrap T (r.start.val + (i.val - 1) * r.step.val)))
      else .error (.jl .boundsError))

theorem scalarRangeIndexSpec_refuted : ¬ ScalarRangeIndexSpec := by
  intro h
  let r : JuliaLean.base.range.StepRange I I :=
    ⟨JInt.wrap .i64 (-10), JInt.wrap .i64 2, JInt.wrap .i64 (-2)⟩
  have hv : ∀ value ∈ steppedRangeValues r.start.val r.step.val 5,
      IntTy.i64.min ≤ value ∧ value ≤ IntTy.i64.max := by decide
  have hg := h.2.2.2 .i64 .u64 r 5 (JInt.wrap .u64 1) (by decide) (by decide) hv
  have hbad : (scalarStepRangeGet r (JInt.wrap .u64 1)).run =
      .error (.jl (.inexactError IntTy.i64.name)) := by decide
  rw [hbad] at hg
  split at hg <;> cases hg

/-- The signed-index wrapper respects a range implementation's documented
ordered-element indexing law; the Bool rejection is independent of that implementation. -/
def OrdinaryRangeIndexSpec : Prop :=
  ∀ (R α : Type) (values : R → List α)
    (get : R → I → JuliaLean.base.range.JlX α)
    (getBool : R → Bool → ExceptT Error JuliaLean.base.range.JlX α),
    (∀ r i, get r i =
      match (values r)[(i.val - 1).toNat]? with
      | some value => if 1 ≤ i.val then .ok value else .error (.jl .boundsError)
      | none => .error (.jl .boundsError)) →
    ∀ r i,
    ((getindexAbstractRange (m := ExceptT Error JuliaLean.base.range.JlX) (fun _ : I => false)
      (fun r i => ExceptT.lift (get r i)) r i).run =
      match (values r)[(i.val - 1).toNat]? with
      | some value =>
        if 1 ≤ i.val then .ok (.ok value) else .error (.jl .boundsError)
      | none => .error (.jl .boundsError)) ∧
    ∀ b, (getindexAbstractRange (fun _ : Bool => true) getBool r b).run =
      .ok (.error (.argument "invalid index of type Bool"))

theorem ordinaryRangeIndexSpec : OrdinaryRangeIndexSpec := by
  intro R α values get getBool hlaw r i
  constructor
  · simp only [getindexAbstractRange, Bool.false_eq_true, ite_false]
    rw [hlaw]
    cases h : (values r)[(i.val - 1).toNat]? with
    | none => rfl
    | some x => by_cases hi : 1 ≤ i.val <;> simp only [hi, ite_true, ite_false] <;> rfl
  · intro b
    rfl


/-- Native signed-range deletion, including both storage-shift directions. -/
abbrev keepatDeleteRange {α : Type} (a : Nat) (r : I × I) : MutationM α Nat :=
  deleteatRange (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
    (fun _ _ => pure ()) (fun r => decide (r.1 > r.2))
    (fun r => r.2 - r.1 + one)
    (deleteatWindow pure mutableLength Subtype.val (· + ·) (· - ·)
      (fun a b => decide (a ≤ b)) (· - ·) mutableCopy mutableCopy
      (deletebeg mutableStorage pure) (deleteend mutableStorage pure)) a r

abbrev KeepatM (α : Type) :=
  ExceptT JuliaLean.base.abstractarray.ArrayError (MutationM α)

@[simp] theorem keepatPure_run (x : β) (old : MutableMemory α) :
    ((pure x : KeepatM α β).run).run old = (.ok (.ok x), old) := rfl

@[simp] theorem keepatBind_run (action : KeepatM α β) (next : β → KeepatM α γ)
    (old : MutableMemory α) :
    ((action >>= next).run).run old =
      match (action.run).run old with
      | (.error e, fresh) => (.error e, fresh)
      | (.ok (.error e), fresh) => (.ok (.error e), fresh)
      | (.ok (.ok x), fresh) => ((next x).run).run fresh := by
  change (action.run >>= ExceptT.bindCont next).run old = _
  rw [stateExcept_bind]
  rcases h : (action.run).run old with ⟨result, fresh⟩
  cases result with
  | error e => rfl
  | ok result => cases result <;> rfl

@[simp] theorem keepatLift_run (action : MutationM α β) (old : MutableMemory α) :
    ((liftM action : KeepatM α β).run).run old =
      ((action.run old).1.map Except.ok, (action.run old).2) := by
  change (action >>= fun x => pure (Except.ok (ε := JuliaLean.base.abstractarray.ArrayError) x)).run old = _
  rw [stateExcept_bind]
  rcases h : action.run old with ⟨result, fresh⟩
  cases result <;> rfl

@[simp] theorem keepatIte_run (p : Prop) [Decidable p]
    (yes no : KeepatM α β) (old : MutableMemory α) :
    (((if p then yes else no).run).run old) =
      if p then ((yes.run).run old) else ((no.run).run old) := by
  split <;> rfl

abbrev keepatStore {α : Type} (a : Nat) (i : I) (x : α) : KeepatM α Unit :=
  liftM (do
    let _ ← setindexScalar (fun _ => true) id pure mutableTypedSet a x i
    pure ())

abbrev nativeKeepatIndices {α : Type} (a : Nat) (indices : List I) : KeepatM α Nat :=
  keepat3129
    (JuliaLean.base.abstractarray.keepAtIndices
      (fun _ => pure one) (fun a => liftM (mutableLength (α := α) a))
      (fun p k => pure (decide (p < k))) (fun i k => pure (decide (i = k)))
      (fun a i => liftM (mutableGet a i)) keepatStore
      (fun _ i => pure (i + one)) (fun i j => pure (i, j))
      (fun a r => liftM (keepatDeleteRange (α := α) a r))) a indices

abbrev nativeKeepatMask {α : Type} (a : Nat) (mask : List Bool) : KeepatM α Nat :=
  keepat3154
    (JuliaLean.base.abstractarray.keepAtMask
      (fun mask => pure (JInt.wrap .i64 (mask.length : Int)))
      (fun a => liftM (mutableLength (α := α) a)) (fun _ => pure one)
      (fun a => liftM (mutableLength (α := α) a))
      (fun _ mask => pure ((List.range mask.length).map
        (fun k : Nat => JInt.wrap .i64 ((k : Int) + 1))))
      (fun mask i => pure (mask[(i.val - 1).toNat]?.getD false))
      (fun a i => liftM (mutableGet a i)) keepatStore
      (fun _ i => pure (i + one)) (fun i j => pure (i, j))
      (fun a r => liftM (keepatDeleteRange (α := α) a r))) a mask

/-- Kept slots, including unassigned reference slots, retain their assignment
state and order under either documented form of keepat!. -/
def KeepatAssignedStateSpec : Prop :=
  ∀ (α : Type) (initial : MutableMemory α) (xs : List (Option α)),
    initial.validVector 0 → initial.contents = xs → xs.length < 2 ^ 62 →
    (∀ indices : List I, indices.Pairwise (fun a b => a.val < b.val) →
      (∀ i ∈ indices, 1 ≤ i.val ∧ i.val ≤ (xs.length : Int)) →
      ∃ next, ((nativeKeepatIndices 0 indices).run).run initial =
        (.ok (.ok 0), next) ∧ next.validVector 0 ∧
        (next.arrays[0]?.map (fun a => a.size.val)) = some (indices.length : Int) ∧
        next.contents = indices.map (fun i => (xs[(i.val - 1).toNat]?).join)) ∧
    (∀ mask : List Bool, mask.length = xs.length →
      ∃ next, ((nativeKeepatMask 0 mask).run).run initial =
        (.ok (.ok 0), next) ∧ next.validVector 0 ∧
        (next.arrays[0]?.map (fun a => a.size.val)) =
          some (((xs.zip mask).filter (fun p => p.2)).length : Int) ∧
        next.contents = ((xs.zip mask).filter (fun p => p.2)).map Prod.fst) ∧
    (∀ mask : List Bool, mask.length < 2 ^ 63 → mask.length ≠ xs.length →
      ((nativeKeepatMask 0 mask).run).run initial =
        (.ok (.error (.julia .boundsError)), initial))

theorem keepatAssignedStateSpec_refuted : ¬ KeepatAssignedStateSpec := by
  intro h
  let xs : List (Option Nat) := [some 10, none, some 30]
  let initial := MutableMemory.initial xs
  obtain ⟨next, he, _⟩ := (h Nat initial xs (by decide) (by decide) (by decide)).1
    [one, JInt.wrap .i64 2] (by decide) (by decide)
  have hbad : (((nativeKeepatIndices (α := Nat) 0 [one, JInt.wrap .i64 2]).run).run initial).1 =
      .error .undefinedReference := by decide
  have := congrArg Prod.fst he
  rw [hbad] at this
  cases this

/-- Fully assigned ordinary vectors retain the selected two-element prefix,
and the Boolean form also preserves an unmoved unassigned slot. -/
def OrdinaryKeepatPrefixSpec : Prop :=
  ∀ (α : Type) (x y z : α),
    (∃ next, (((nativeKeepatIndices 0 [one, JInt.wrap .i64 2]).run).run
      (MutableMemory.initial [some x, some y, some z])) = (.ok (.ok 0), next) ∧
      next.contents = [some x, some y]) ∧
    (∃ next, (((nativeKeepatMask 0 [true, true, false]).run).run
      (MutableMemory.initial [some x, some y, some z])) = (.ok (.ok 0), next) ∧
      next.contents = [some x, some y]) ∧
    (∃ next, (((nativeKeepatMask 0 [true, true, false]).run).run
      (MutableMemory.initial [some x, none, some z])) = (.ok (.ok 0), next) ∧
      next.contents = [some x, none])

def keepatPrefixState (x : α) (y : Option α) : MutableMemory α :=
  ⟨[[some x, y, none] ++ List.replicate 32 none],
    [⟨(0, one), JInt.wrap .i64 2⟩]⟩

theorem keepatIndices_prefix_program :
    nativeKeepatIndices (α := α) 0 [one, JInt.wrap .i64 2] =
      (do
        let _ ← liftM (mutableGet (α := α) 0 one)
        let _ ← liftM (mutableGet (α := α) 0 (JInt.wrap .i64 2))
        let last ← liftM (mutableLength (α := α) 0)
        let _ ← liftM (keepatDeleteRange (α := α) 0 (JInt.wrap .i64 3, last))
        pure 0 : KeepatM α Nat) := by
  have h12 : one + one = JInt.wrap .i64 2 := by decide
  have h23 : JInt.wrap .i64 2 + one = JInt.wrap .i64 3 := by decide
  have hlt : one < JInt.wrap .i64 2 := by decide
  simp [nativeKeepatIndices, keepat3129, JuliaLean.base.abstractarray.keepAtIndices,
    List.forIn_cons, List.forIn_nil, bind_assoc, h12, h23, hlt]

theorem keepatMask_prefix_program :
    nativeKeepatMask (α := α) 0 [true, true, false] =
      (do
        let n ← liftM (mutableLength (α := α) 0)
        if (3 : Int) != n.val then throw (.julia .boundsError)
        else do
          let last ← liftM (mutableLength (α := α) 0)
          liftM (keepatDeleteRange (α := α) 0 (JInt.wrap .i64 3, last)) : KeepatM α Nat) := by
  have h1 : JInt.wrap .i64 1 = one := rfl
  have h12 : one + one = JInt.wrap .i64 2 := by decide
  have h23 : JInt.wrap .i64 2 + one = JInt.wrap .i64 3 := by decide
  have h3 : (JInt.wrap .i64 3).val = 3 := by decide
  have h1v : one.val = 1 := by decide
  have h2v : (JInt.wrap .i64 2).val = 2 := by decide
  simp [nativeKeepatMask, keepat3154, JuliaLean.base.abstractarray.keepAtMask,
    List.forIn_cons, List.forIn_nil, bind_assoc, h1, h12, h23, h3, h1v, h2v, List.range_succ]

@[simp] theorem mutation_map_run (f : β → γ) (action : StateM (MutableMemory α) β)
    (s : MutableMemory α) :
    (f <$> action).run s = (f (action.run s).1, (action.run s).2) := rfl

set_option maxRecDepth 200000 in
theorem keepatDelete_prefix_run (x : α) (y z : Option α) :
    (keepatDeleteRange 0 (JInt.wrap .i64 3, JInt.wrap .i64 3)).run
      (MutableMemory.initial [some x, y, z]) =
      (.ok 0, keepatPrefixState x y) := by
  have hd : JInt.wrap .i64 3 - JInt.wrap .i64 3 + one = one := by decide
  have he : decide (JInt.wrap .i64 3 > JInt.wrap .i64 3) = false := by decide
  have h13 : one ≤ JInt.wrap .i64 3 := by decide
  have h33 : JInt.wrap .i64 3 ≤ JInt.wrap .i64 3 := by decide
  have hp : JInt.wrap .i64 3 + one = JInt.wrap .i64 4 := by decide
  have h43 : JInt.wrap .i64 4 - JInt.wrap .i64 3 = one := by decide
  have h41 : JInt.wrap .i64 4 - one = JInt.wrap .i64 3 := by decide
  have h30 : JInt.wrap .i64 3 - JInt.wrap .i64 3 = zero := by decide
  have hb : ¬ JInt.wrap .i64 2 * JInt.wrap .i64 3 + one ≤ JInt.wrap .i64 3 := by decide
  have hu : ¬ JInt.rem .u64 one > JInt.rem .u64 (JInt.wrap .i64 3) := by decide
  have h32 : JInt.wrap .i64 3 - one = JInt.wrap .i64 2 := by decide
  have h23 : JInt.wrap .i64 2 + one = JInt.wrap .i64 3 := by decide
  have h14 : one + JInt.wrap .i64 3 = JInt.wrap .i64 4 := by decide
  have hr : intRange (JInt.wrap .i64 3) (JInt.wrap .i64 3) = [JInt.wrap .i64 3] := by decide
  have hv0 : zero.val = 0 := by decide
  have hv1 : one.val = 1 := by decide
  have hv3 : (JInt.wrap .i64 3).val = 3 := by decide
  have hw1 : wrapInt .i64 1 = 1 := by decide
  have hw2 : wrapInt .i64 2 = 2 := by decide
  have hw3 : wrapInt .i64 3 = 3 := by decide
  have hw4 : wrapInt .i64 4 = 4 := by decide
  simp [keepatDeleteRange, deleteatRange, deleteatWindow, deleteend,
    mutableStorage, mutableLength, mutableVector, mutableUnset, unsetindexInt,
    mutableBounds, mutableInBounds, mutableMemoryref, mutableRef, mutableCopy,
    unsafeCopyArray, memoryWrite, memoryRead, keepatPrefixState, MutableMemory.initial,
    stateExcept_bind, stateExcept_pure, mutation_get_run, mutation_modify_run,
    List.forIn_cons, List.forIn_nil,
    hd, he, h13, h33, hp, h43, h41, h30, hb, hu, h32, h23, h14, hr, hv0, hv1, hv3,
    hw1, hw2, hw3, hw4, mutation_map_run]
  rfl

theorem keepatRead_first_run (x y z : α) :
    (mutableGet 0 one).run (MutableMemory.initial [some x, some y, some z]) =
      (.ok x, MutableMemory.initial [some x, some y, some z]) := by
  have hb : one ≤ JInt.wrap .i64 3 := by decide
  have hv : one.val = 1 := by decide
  simp [mutableGet, stateExcept_bind, mutableVector_run, MutableMemory.initial,
    hb, hv, memoryRead, mutation_get_run, stateExcept_pure]

theorem keepatRead_second_run (x y z : α) :
    (mutableGet 0 (JInt.wrap .i64 2)).run (MutableMemory.initial [some x, some y, some z]) =
      (.ok y, MutableMemory.initial [some x, some y, some z]) := by
  have hb : JInt.wrap .i64 2 ≤ JInt.wrap .i64 3 := by decide
  have hv1 : one.val = 1 := by decide
  have hv2 : (JInt.wrap .i64 2).val = 2 := by decide
  simp [mutableGet, stateExcept_bind, mutableVector_run, MutableMemory.initial,
    hb, hv1, hv2, memoryRead, mutation_get_run, stateExcept_pure]

theorem keepatMask_prefix_run (x : α) (y z : Option α) :
    ((nativeKeepatMask 0 [true, true, false]).run).run
      (MutableMemory.initial [some x, y, z]) =
      (.ok (.ok 0), keepatPrefixState x y) := by
  let initial := MutableMemory.initial [some x, y, z]
  have hl : (mutableLength (α := α) 0).run initial = (.ok (JInt.wrap .i64 3), initial) :=
    mutableLength_run initial 0 ⟨(0, one), JInt.wrap .i64 3⟩ rfl
  rw [keepatMask_prefix_program, keepatBind_run, keepatLift_run, hl]
  simp only [Except.map]
  have hv : (JInt.wrap .i64 3).val = 3 := by decide
  simp only [hv, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rw [keepatBind_run, keepatLift_run, hl]
  simp only [Except.map]
  rw [keepatLift_run, keepatDelete_prefix_run]
  rfl

set_option maxRecDepth 32768 in
theorem ordinaryKeepatPrefixSpec : OrdinaryKeepatPrefixSpec := by
  intro α x y z
  refine ⟨⟨keepatPrefixState x (some y), ?_, rfl⟩,
    ⟨keepatPrefixState x (some y), ?_, rfl⟩,
    ⟨keepatPrefixState x none, ?_, rfl⟩⟩
  · let initial := MutableMemory.initial [some x, some y, some z]
    have hl : (mutableLength (α := α) 0).run initial = (.ok (JInt.wrap .i64 3), initial) :=
      mutableLength_run initial 0 ⟨(0, one), JInt.wrap .i64 3⟩ rfl
    rw [keepatIndices_prefix_program, keepatBind_run, keepatLift_run, keepatRead_first_run]
    simp only [Except.map]
    rw [keepatBind_run, keepatLift_run, keepatRead_second_run]
    simp only [Except.map]
    rw [keepatBind_run, keepatLift_run, hl]
    simp only [Except.map]
    rw [keepatBind_run, keepatLift_run, keepatDelete_prefix_run]
    rfl
  · exact keepatMask_prefix_run x (some y) (some z)
  · exact keepatMask_prefix_run x none (some z)

/-- Cartesian reads neither change memory nor read a cell before the complete
tuple passes the bounds and linear-index checks. -/
def CartesianReadSpec : Prop :=
  ∀ (α : Type) (slots : I → Option α)
    (bounds : List I → Bool) (linear : List I → Except Error I)
    (i₁ i₂ : I) (rest : List I),
    let indices := i₁ :: i₂ :: rest
    let operation := getindexCartesian
      (fun (_ : Unit) js => slotLift (if bounds js then .ok () else .error .bounds))
      (fun _ js => slotLift (linear js)) (fun _ i => slotRead i) () i₁ i₂ rest
    (bounds indices = false → operation.run slots = (.error .bounds, slots)) ∧
    (∀ e, bounds indices = true → linear indices = .error e →
      operation.run slots = (.error e, slots)) ∧
    (∀ i, bounds indices = true → linear indices = .ok i →
      (∀ x, slots i = some x → operation.run slots = (.ok x, slots)) ∧
      (slots i = none → operation.run slots = (.error .undefinedReference, slots)))

theorem cartesianReadSpec : CartesianReadSpec := by
  intro α slots bounds linear i₁ i₂ rest indices operation
  have run : operation.run slots =
      if bounds indices then
        match linear indices with
        | .error e => (.error e, slots)
        | .ok i => ((match slots i with
          | some x => .ok x
          | none => .error .undefinedReference), slots)
      else (.error .bounds, slots) := by
    cases hb : bounds indices <;> cases hl : linear indices <;>
      simp [operation, indices, getindexCartesian, slotRead, slotLift, hb, hl,
        ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
        StateT.bind, StateT.pure, Bind.bind, Pure.pure] at *
  refine ⟨?_, ?_, ?_⟩
  · intro hb; rw [run, hb]; rfl
  · intro e hb hl; rw [run, hb, hl]; rfl
  · intro i hb hl
    constructor
    · intro x hx; simp [run, hb, hl, hx]
    · intro hx; simp [run, hb, hl, hx]

/-- Tuple entries retain the distinction relevant to Julia dispatch. -/
inductive IndcopyTupleIndex (R : Type) where
  | range (value : R)
  | vector (values : List I)

def indcopyIndexValues (values : R → List I) : IndcopyTupleIndex R → List I
  | .range r => values r
  | .vector xs => xs

def indcopyRangeEntry : IndcopyTupleIndex R → Option R
  | .range r => some r
  | .vector _ => none

/-- Core tuple/vector indexing, including bounds checking. -/
def indcopyCoreGet (xs : List α) (i : I) : Jl α :=
  if 1 ≤ i.val then
    match xs[(i.val - 1).toNat]? with
    | none => .error .boundsError
    | some x => .ok x
  else .error .boundsError

/-- The tuple-of-ranges method is the actual source definition. A tuple with
any index-vector entry has no applicable method and raises Core's MethodError
at this dispatch, as confirmed on the pinned nightly. Range-valued _findin and
range slicing are external methods from range.jl. -/
def tupleIndcopy {R : Type} (values : R → List I)
    (find : R → I → I → Jl R) (get : R → R → Jl R)
    (dims : List I) (indices : List (IndcopyTupleIndex R)) :
    Jl (List (List I) × List (List I)) :=
  match indices.mapM indcopyRangeEntry with
  | none => .error (.methodError "indcopy")
  | some ranges =>
    (indcopyTuple
      (fun dims : List I => JInt.wrap .i64 (dims.length : Int)) indcopyCoreGet
      (fun indices : List R => JInt.wrap .i64 (indices.length : Int)) indcopyCoreGet
      find get pure dims ranges).map (fun p => (p.1.map values, p.2.map values))

/-- Destination positions and retained source values, independent of indcopy.
The last index collection uses all remaining source dimensions. -/
def indcopyExpected (dims : List I) (indices : List (List I)) :
    List (List I) × List (List I) :=
  let bound := fun axis : Nat =>
    if axis + 1 < indices.length then (dims[axis]?.map Subtype.val).getD 0
    else ((dims.drop axis).map Subtype.val).prod
  let dst := indices.zipIdx |>.map (fun (xs, axis) =>
    xs.zipIdx |>.filterMap (fun (x, k) =>
      if 1 ≤ x.val ∧ x.val ≤ bound axis then some (JInt.wrap .i64 ((k : Int) + 1)) else none))
  let src := indices.zipIdx |>.map (fun (xs, axis) =>
    xs.filter (fun x => decide (1 ≤ x.val ∧ x.val ≤ bound axis)))
  (dst, src)

/-- The range primitives' documented interfaces describe their yielded values,
including the positions of the intersection and valid range slicing. -/
def IndcopyRangeLaws {R : Type} (values : R → List I)
    (find : R → I → I → Jl R) (get : R → R → Jl R) : Prop :=
  (∀ r lo hi, (find r lo hi).map values =
    .ok ((values r).zipIdx |>.filterMap (fun (x, k) =>
      if lo.val ≤ x.val ∧ x.val ≤ hi.val then some (JInt.wrap .i64 ((k : Int) + 1)) else none))) ∧
  (∀ r is, (∀ i ∈ values is, 1 ≤ i.val ∧ i.val ≤ ((values r).length : Int)) →
    (get r is).map values =
      (values is).mapM (indcopyCoreGet (values r)))

/-- Both tuples of ranges and tuples containing integer index vectors accepted
by get! must compute the exact retained positions and source values. -/
def TupleVectorIndcopySpec : Prop :=
  ∀ (R : Type) (values : R → List I) (find : R → I → I → Jl R) (get : R → R → Jl R),
    IndcopyRangeLaws values find get →
    ∀ dims indices,
      0 < indices.length → indices.length ≤ dims.length →
      (∀ n ∈ dims, 0 ≤ n.val) →
      (((dims.map Subtype.val).prod < 2 ^ 63) ∧
        ∀ axis ∈ indices.map (indcopyIndexValues values), axis.length < 2 ^ 63) →
      tupleIndcopy values find get dims indices =
        .ok (indcopyExpected dims (indices.map (indcopyIndexValues values)))

theorem tupleVectorIndcopySpec_refuted : ¬ TupleVectorIndcopySpec := by
  intro h
  let values : Empty → List I := fun r => nomatch r
  let find : Empty → I → I → Jl Empty := fun r => nomatch r
  let get : Empty → Empty → Jl Empty := fun r => nomatch r
  have hlaws : IndcopyRangeLaws values find get := by
    constructor
    · intro r; nomatch r
    · intro r; nomatch r
  have hh := h Empty values find get hlaws [JInt.wrap .i64 3]
    [.vector [one, JInt.wrap .i64 2]] (by decide) (by decide) (by decide) (by decide)
  simp only [tupleIndcopy, List.mapM_cons, indcopyRangeEntry, Option.bind_none] at hh
  cases hh

/-- The exact absent dispatch also propagates through the real get! caller,
after its mandatory destination fill and source size query. -/
theorem tupleVectorGet_methodError {X A E V R : Type}
    (values : R → List I) (find : R → I → I → Jl R) (getRange : R → R → Jl R)
    (fill : X → E → Jl Unit) (size : A → Jl (List I))
    (get : A → List (List I) → Jl V) (set : X → List (List I) → V → Jl Unit)
    (x : X) (a : A) (default : E) (dims : List I) (vector : List I)
    (rest : List (IndcopyTupleIndex R))
    (hf : fill x default = .ok ()) (hs : size a = .ok dims) :
    JuliaLean.base.abstractarray.getIndexList fill size (tupleIndcopy values find getRange)
      get set x a (.vector vector :: rest) default = .error (.methodError "indcopy") := by
  simp [JuliaLean.base.abstractarray.getIndexList, hf, hs, tupleIndcopy, indcopyRangeEntry,
    List.mapM_cons, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Core allocates a separate memory object; this operation has no source-array
parameter that could limit freshness to only one existing allocation. -/
def heapCopyAllocate (n : I) : VectorM α Nat :=
  if n.val < 0 then throw (.argument "invalid Memory dimensions")
  else heapAllocate n.val.toNat

/-- copy(::Array) with a shared heap of live memory objects. The memory copy
preserves unassigned slots, and the Core header constructor retains the type
and dimensions while referencing the newly allocated object. -/
abbrev heapFreshCopy {Tag α : Type} (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  copyArray (fun a => pure (a.handle, one))
    (fun a => pure (JInt.wrap .i64 (a.dimensions.prod : Int)))
    (fun _ n => heapCopyAllocate n) (fun handle => pure (handle, one))
    (heapCopyReferences (fun x => .ok x)) (fun a => pure a.dimensions)
    (fun ref dims => pure ⟨ref.1, src.elementType, dims, dims.map (fun n => (1, n))⟩) src

theorem heapFreshCopy_run {Tag α : Type} (heap : VectorHeap α) (src : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[src.handle]? = some xs)
    (hl : src.dimensions.prod = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapFreshCopy src).run heap =
      .ok (⟨heap.length, src.elementType, src.dimensions,
        src.dimensions.map (fun n => (1, n))⟩, heap ++ [xs]) := by
  have hv : (JInt.wrap .i64 (src.dimensions.prod : Int)).val = xs.length := by
    rw [hl]
    exact collectorLengthFits xs.length hn
  have hslt : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  let allocated : VectorHeap α := heap ++ [List.replicate xs.length none]
  have hsrc : allocated[src.handle]? = some xs := by
    simpa [allocated, List.getElem?_append_left hslt] using hs
  have hdest : allocated[heap.length]? = some (List.replicate xs.length none) := by
    simp [allocated]
  have hm : ∀ ys : List (Option α),
      ys.mapM (fun x => Except.ok (ε := Error) x) = .ok ys := by
    intro ys
    induction ys with
    | nil => rfl
    | cons x ys ih =>
      simp [List.mapM_cons, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]
  have hc :
      (heapCopyReferences (fun x => Except.ok (ε := Error) x)
        (heap.length, one) (src.handle, one)
        (JInt.wrap .i64 (src.dimensions.prod : Int))).run allocated =
      .ok ((), heap ++ [xs]) := by
    rw [hl, heapCopyReferences_whole_run (fun x => Except.ok (ε := Error) x)
      allocated heap.length src.handle xs (List.replicate xs.length none)
      hsrc hdest (by simp) hn, hm xs]
    simp [Except.map, allocated, List.set_append_right]
  simp only [heapFreshCopy, copyArray, heapCopyAllocate, vector_bind_run, vector_pure_run,
    hv, Int.not_lt.mpr (Int.natCast_nonneg xs.length), ite_false]
  simp only [heapAllocate_run, Int.toNat_natCast]
  rw [hc]

def SharedHeapArrayCopySpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    ∃ dest next, (heapFreshCopy src).run heap = .ok (dest, next) ∧
      dest.elementType = src.elementType ∧ dest.dimensions = src.dimensions ∧
      next[dest.handle]? = some xs ∧
      (∀ handle, handle < heap.length → dest.handle ≠ handle ∧ next[handle]? = heap[handle]?)

theorem sharedHeapArrayCopySpec : SharedHeapArrayCopySpec := by
  intro Tag α heap src xs hs hl hn
  refine ⟨_, _, heapFreshCopy_run heap src xs hs hl hn, rfl, rfl, ?_, ?_⟩
  · simp
  · intro handle hh
    exact ⟨Nat.ne_of_gt hh, List.getElem?_append_left hh⟩

/-- Reversing a valid index reflects it through the two linear endpoints, including wide indices. -/
def ReverseIndexReflectionSpec : Prop :=
  ∀ (A : Type) (firstLinear lastLinear : A → I) (a : A)
    (t : IntTy) (i : JInt t),
    (firstLinear a).val ≤ i.val → i.val ≤ (lastLinear a).val →
    (reverseind firstLinear lastLinear (JuliaLean.base.int.binop JuliaLean.base.int.sub)
      a i).val = (firstLinear a).val + (lastLinear a).val - i.val

theorem reverseIndexReflectionSpec_refuted : ¬ ReverseIndexReflectionSpec := by
  intro h
  have heq := h Unit (fun _ => JInt.wrap .i64 1)
    (fun _ => JInt.wrap .i64 (2 ^ 63 - 1)) () .i128 (JInt.wrap .i128 1)
    (by decide) (by decide)
  have hne :
      (reverseind (fun _ : Unit => JInt.wrap .i64 1)
        (fun _ => JInt.wrap .i64 (2 ^ 63 - 1))
        (JuliaLean.base.int.binop JuliaLean.base.int.sub) () (JInt.wrap .i128 1)).val ≠
        (JInt.wrap .i64 1).val + (JInt.wrap .i64 (2 ^ 63 - 1)).val -
          (JInt.wrap .i128 1).val := by decide
  exact hne heq

/-- Scalar searches return every successful position exactly once. -/
def ScalarFindallSpec : Prop :=
  (∀ (x : Bool), (findallBool x).Nodup ∧
    ∀ k, k ∈ findallBool x ↔ x = true ∧ k = one) ∧
  (∀ (α : Type) (test : α → Bool) (x : α), (findallNumber test x).Nodup ∧
    ∀ k, k ∈ findallNumber test x ↔ test x = true ∧ k = one) ∧
  (∀ (α Collection : Type) (contains : α → Collection → Bool)
    (collection : Collection) (x : α), (findallInNumber contains collection x).Nodup ∧
    ∀ k, k ∈ findallInNumber contains collection x ↔
      contains x collection = true ∧ k = one)

theorem scalarFindallSpec : ScalarFindallSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    cases x <;> simp [findallBool]
  · intro α test x
    cases h : test x <;> simp [findallNumber, h]
  · intro α Collection contains collection x
    cases h : contains x collection <;> simp [findallInNumber, h]

/-- Searches in a one-based integer interval return precisely its matching first key. -/
def OneToFirstSearchSpec : Prop :=
  (∀ (x stop k : Int),
    findfirstOneTo (m := Except Error) id id (fun x => pure x) x stop = .ok (some k) ↔
      k = x ∧ 1 ≤ k ∧ k ≤ stop) ∧
  (∀ (x stop : Int),
    findfirstOneTo (m := Except Error) id id (fun x => pure x) x stop = .ok none ↔
      x < 1 ∨ stop < x) ∧
  (∀ (stop : Int), findfirstZeroOneTo (K := Int) stop = none) ∧
  (∀ (stop k : Int),
    findfirstOneOneTo (m := Except Error) (fun n : Int => decide (n < 1))
      (fun _ => pure (1 : Int)) stop = .ok (some k) ↔ k = 1 ∧ 1 ≤ stop)

theorem oneToFirstSearchSpec : OneToFirstSearchSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x stop k
    by_cases h : 1 ≤ x ∧ x ≤ stop
    · simp [findfirstOneTo, h, id, Bind.bind, Pure.pure, Except.bind, Except.pure]
      omega
    · simp [findfirstOneTo, h, id, Bind.bind, Pure.pure, Except.bind, Except.pure]
      omega
  · intro x stop
    by_cases h : 1 ≤ x ∧ x ≤ stop <;>
      simp [findfirstOneTo, h, id, Bind.bind, Pure.pure, Except.bind, Except.pure] <;> omega
  · intro stop
    rfl
  · intro stop k
    by_cases h : stop < 1 <;>
      simp [findfirstOneOneTo, h, Bind.bind, Pure.pure, Except.bind, Except.pure] <;> omega

/-- Native integer storage has no padding: comparing all bytes of equal-length
arrays returns zero exactly when their stored integer values agree. -/
def BitIntegerEqualitySpec : Prop :=
  (∀ (t : IntTy) (A : Type) (values : A → List (JInt t))
      (dims : A → List Nat) (elementSize : I)
      (memcmp : A → A → I → JInt .i32),
    (∀ a b, dims a = dims b → (values a).length = (values b).length) →
    (∀ a b, (values a).length = (values b).length →
      ((memcmp a b (elementSize * JInt.wrap .i64 ((values a).length : Int))).val = 0 ↔
        values a = values b)) →
    ∀ a b, equalBitInteger2171 (m := Id) dims (fun x y => decide (x = y))
      id (fun _ => ()) id (fun a => JInt.wrap .i64 ((values a).length : Int))
      elementSize memcmp (fun _ => ()) a b = true ↔
      dims a = dims b ∧ values a = values b) ∧
  (∀ (t : IntTy) (A : Type) (values : A → List (JInt t))
      (elementSize : I) (memcmp : A → A → I → JInt .i32),
    (∀ a, (values a).length < 2 ^ 63) →
    (∀ a b, (values a).length = (values b).length →
      ((memcmp a b (elementSize * JInt.wrap .i64 ((values a).length : Int))).val = 0 ↔
        values a = values b)) →
    ∀ a b, equalBitIntegerVector (m := Id) id (fun _ => ()) id
      (fun a => JInt.wrap .i64 ((values a).length : Int)) elementSize
      memcmp (fun _ => ()) a b = true ↔ values a = values b)

theorem bitIntegerEqualitySpec : BitIntegerEqualitySpec := by
  constructor
  · intro t A values dims elementSize memcmp hshape hmemcmp a b
    dsimp only [equalBitInteger2171, Bind.bind, Pure.pure, Functor.map]
    by_cases hs : dims a = dims b
    · simp only [hs, decide_true, ite_true, id_eq, true_and]
      exact (beq_iff_eq).trans (hmemcmp a b (hshape a b hs))
    · simp [hs]
  · intro t A values elementSize memcmp hfit hmemcmp a b
    have heq : JInt.wrap .i64 ((values a).length : Int) =
        JInt.wrap .i64 ((values b).length : Int) ↔
        (values a).length = (values b).length := by
      constructor
      · intro h
        have hv := congrArg (fun n : I => n.val) h
        rw [collectorLengthFits _ (hfit a), collectorLengthFits _ (hfit b)] at hv
        exact_mod_cast hv
      · intro h
        rw [h]
    dsimp only [equalBitIntegerVector, Bind.bind, Pure.pure, Functor.map]
    by_cases hl : (values a).length = (values b).length
    · rw [if_pos (heq.mpr hl)]
      simp only [id_eq]
      exact (beq_iff_eq).trans (hmemcmp a b hl)
    · have hm : values a ≠ values b := fun h => hl (congrArg List.length h)
      simp [heq, hl, hm]

theorem getindexColon_vector_run {α A : Type} (heap next final : VectorHeap α)
    (a x : A) (n : I) (length : A → VectorM α I)
    (similar : A → I → VectorM α A)
    (copy : A → I → A → I → I → VectorM α Unit)
    (hl : (length a).run heap = .ok (n, heap))
    (ha : (similar a n).run heap = .ok (x, next))
    (hc : 0 < n.val → (copy x one a one n).run next = .ok ((), final))
    (hz : ¬ 0 < n.val → final = next) :
    (getindexColon length similar copy a).run heap = .ok (x, final) := by
  simp only [getindexColon, vector_bind_run, hl, ha]
  split
  · rename_i hp
    simp only [vector_bind_run, hc hp, vector_pure_run]
  · rename_i hp
    simp only [vector_pure_run, hz hp]

theorem unsafeCopyArray_vector_run {Tag α : Type} (heap next : VectorHeap α)
    (dest source : HeapArray Tag) (doffs soffs n : I) (hn : n.val ≠ 0)
    (hc : (heapCopyReferences (fun x => Except.ok (ε := Error) x)
      (dest.handle, doffs) (source.handle, soffs) n).run heap = .ok ((), next)) :
    (do
      let _ ← unsafeCopyArray (fun n : I => decide (n.val = 0))
        (fun a i => pure (a.handle, i)) (fun a i => pure (a.handle, i))
        (heapCopyReferences (fun x => .ok x)) dest doffs source soffs n
      pure () : VectorM α Unit).run heap = .ok ((), next) := by
  simp only [unsafeCopyArray, hn, decide_false, Bool.false_eq_true, ite_false,
    vector_bind_run, vector_pure_run, hc]

def heapColonLength {Tag α : Type} (a : HeapArray Tag) : VectorM α I :=
  pure (JInt.wrap .i64 (a.dimensions.prod : Int))

def heapColonSimilar {Tag α : Type} (a : HeapArray Tag) (n : I) :
    VectorM α (HeapArray Tag) :=
  similar418 (fun n => heapAllocateIntDims a.elementType [n]) a n

def heapColonMemoryCopy {Tag α : Type} (dest : HeapArray Tag) (doffs : I)
    (source : HeapArray Tag) (soffs n : I) : VectorM α Unit := do
  let _ ← unsafeCopyArray (fun n : I => decide (n.val = 0))
    (fun a i => pure (a.handle, i)) (fun a i => pure (a.handle, i))
    (heapCopyReferences (fun x => .ok x)) dest doffs source soffs n
  pure ()

/-- Colon indexing preserves the element type and uses the native vector allocator. -/
abbrev heapColonCopy {Tag α : Type} (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  getindexColon heapColonLength heapColonSimilar heapColonMemoryCopy src

attribute [local irreducible] heapAllocateIntDims JInt.wrap wrapInt

theorem heapColonSimilar_allocate {Tag α : Type} (heap : VectorHeap α)
    (src : HeapArray Tag) (n : I) :
    (heapColonSimilar (α := α) src n).run heap =
      (heapAllocateIntDims src.elementType [n]).run heap := rfl

theorem colonSingletonFits (n : Nat) (hn : n < 2 ^ 63) :
    heapDimensionsFit [n] = true := by
  simpa only [heapDimensionsFit, List.all_cons, List.all_nil, Bool.and_true,
    decide_eq_true_eq] using hn

theorem colonSingletonProduct (n : Nat) (hn : n < 2 ^ 63) :
    [n].prod < 2 ^ 63 := by
  simpa only [List.prod_cons, List.prod_nil, Nat.mul_one] using hn

theorem colonSingletonAllocation {Tag α : Type} (heap : VectorHeap α)
    (target : Tag) (n : Nat) :
    freshShapeAllocation target [n] heap =
      .ok (⟨heap.length, target, [n], [(1, n)]⟩,
        heap ++ [List.replicate n none]) := by
  simp only [freshShapeAllocation, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Nat.mul_one]

theorem heapColonSimilar_nat_run {Tag α : Type} (heap : VectorHeap α)
    (src : HeapArray Tag) (n : Nat) (hn : n < 2 ^ 63) :
    (heapColonSimilar (α := α) src (JInt.wrap .i64 (n : Int))).run heap =
      .ok (⟨heap.length, src.elementType, [n], [(1, n)]⟩,
        heap ++ [List.replicate n none]) :=
  (heapColonSimilar_allocate heap src _).trans
    ((heapAllocateIntDims_nat_run src.elementType [n] heap
      (colonSingletonFits n hn) (colonSingletonProduct n hn)).trans
      (colonSingletonAllocation heap src.elementType n))

theorem heapColonSimilar_run {Tag α : Type} (heap : VectorHeap α)
    (src : HeapArray Tag) (n : Nat) (hl : src.dimensions.prod = n) (hn : n < 2 ^ 63) :
    (heapColonSimilar (α := α) src (JInt.wrap .i64 (src.dimensions.prod : Int))).run heap =
      .ok (⟨heap.length, src.elementType, [n], [(1, n)]⟩,
        heap ++ [List.replicate n none]) := by
  rw [hl]
  exact heapColonSimilar_nat_run heap src n hn

theorem heapColonReferences_run {Tag α : Type} (heap : VectorHeap α)
    (src : HeapArray Tag) (xs : List (Option α))
    (hs : heap[src.handle]? = some xs) (hl : src.dimensions.prod = xs.length)
    (hn : xs.length < 2 ^ 63) :
    (heapCopyReferences (fun x => Except.ok (ε := Error) x)
      (heap.length, one) (src.handle, one)
      (JInt.wrap .i64 (src.dimensions.prod : Int))).run
      (heap ++ [List.replicate xs.length none]) = .ok ((), heap ++ [xs]) := by
  have hslt : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  have hsrc : (heap ++ [List.replicate xs.length none])[src.handle]? = some xs := by
    simpa [List.getElem?_append_left hslt] using hs
  have hdest : (heap ++ [List.replicate xs.length none])[heap.length]? =
      some (List.replicate xs.length none) := by simp
  have hm : ∀ ys : List (Option α),
      ys.mapM (fun x => Except.ok (ε := Error) x) = .ok ys := by
    intro ys
    induction ys with
    | nil => rfl
    | cons x ys ih =>
      simp [List.mapM_cons, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]
  rw [hl, heapCopyReferences_whole_run (fun x => Except.ok (ε := Error) x)
    (heap ++ [List.replicate xs.length none]) heap.length src.handle xs
    (List.replicate xs.length none) hsrc hdest (by simp) hn, hm xs]
  simp [Except.map, List.set_append_right]

theorem heapColonMemoryCopy_run {Tag α : Type} (heap : VectorHeap α)
    (src : HeapArray Tag) (xs : List (Option α))
    (hs : heap[src.handle]? = some xs) (hl : src.dimensions.prod = xs.length)
    (hn : xs.length < 2 ^ 63)
    (hp : 0 < (JInt.wrap .i64 (src.dimensions.prod : Int)).val) :
    (heapColonMemoryCopy (⟨heap.length, src.elementType, [xs.length],
      [(1, xs.length)]⟩ : HeapArray Tag) one src one
      (JInt.wrap .i64 (src.dimensions.prod : Int))).run
      (heap ++ [List.replicate xs.length none]) = .ok ((), heap ++ [xs]) := by
  unfold heapColonMemoryCopy
  apply unsafeCopyArray_vector_run
  · omega
  · exact heapColonReferences_run heap src xs hs hl hn

theorem heapColonCopy_run {Tag α : Type} (heap : VectorHeap α) (src : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[src.handle]? = some xs)
    (hl : src.dimensions.prod = xs.length) (hn : xs.length < 2 ^ 63) :
    (heapColonCopy src).run heap =
      .ok (⟨heap.length, src.elementType, [xs.length], [(1, xs.length)]⟩, heap ++ [xs]) := by
  apply getindexColon_vector_run heap (heap ++ [List.replicate xs.length none])
    (heap ++ [xs]) src
    ⟨heap.length, src.elementType, [xs.length], [(1, xs.length)]⟩
    (JInt.wrap .i64 (src.dimensions.prod : Int))
    heapColonLength heapColonSimilar heapColonMemoryCopy rfl
  · exact heapColonSimilar_run heap src xs.length hl hn
  · exact heapColonMemoryCopy_run heap src xs hs hl hn
  · intro hp
    have hv : (JInt.wrap .i64 (src.dimensions.prod : Int)).val = xs.length := by
      rw [hl]
      exact collectorLengthFits xs.length hn
    have hempty : xs.length = 0 := by rw [hv] at hp; omega
    have hxs : xs = [] := by simpa using hempty
    simp [hxs]

def ColonArrayCopySpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α)),
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    ∃ dest next, (heapColonCopy src).run heap = .ok (dest, next) ∧
      dest.elementType = src.elementType ∧ dest.dimensions = [xs.length] ∧
      dest.axes = [(1, xs.length)] ∧ next[dest.handle]? = some xs ∧
      (∀ handle, handle < heap.length → dest.handle ≠ handle ∧ next[handle]? = heap[handle]?)

theorem colonArrayCopySpec : ColonArrayCopySpec := by
  intro Tag α heap src xs hs hl hn
  refine ⟨_, _, heapColonCopy_run heap src xs hs hl hn, rfl, rfl, rfl, ?_, ?_⟩
  · simp
  · intro handle hh
    exact ⟨Nat.ne_of_gt hh, List.getElem?_append_left hh⟩

theorem findlast_none_iff (test : α → Bool) (pairs : List (K × α)) :
    findlast (m := Id) List.reverse test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false := by
  change findfirst (m := Id) test pairs.reverse = none ↔ _
  have h := findfirst_none_iff test pairs.reverse
  simpa only [List.mem_reverse] using h

/-- Boolean searches return a true element at the first or last matching position,
    and return nothing exactly when every element is false. -/
def BooleanSearchPositionsSpec : Prop :=
  ∀ (K : Type) (pairs : List (K × Bool)),
    (findfirstBool (m := Id) (findfirst (m := Id)) pairs = none ↔
      ∀ p ∈ pairs, p.2 = false) ∧
    (∀ key, findfirstBool (m := Id) (findfirst (m := Id)) pairs = some key →
      firstMatch id pairs key) ∧
    (findlastBool (m := Id) (findlast (m := Id) List.reverse) pairs = none ↔
      ∀ p ∈ pairs, p.2 = false) ∧
    (∀ key, findlastBool (m := Id) (findlast (m := Id) List.reverse) pairs = some key →
      lastMatch id pairs key)

theorem booleanSearchPositionsSpec : BooleanSearchPositionsSpec := by
  intro K pairs
  exact ⟨findfirst_none_iff id pairs, findfirst_firstMatch id pairs,
    findlast_none_iff id pairs, findlast_lastMatch id pairs⟩

def LastSearchComplete : Prop :=
  ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)),
    findlast (m := Id) List.reverse test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false

theorem lastSearchComplete : LastSearchComplete := fun _ _ => findlast_none_iff


section
open JuliaLean.Proofs.base.int

private theorem midpoint_difference_pattern {t : IntTy} (lo hi : JInt t) (h : lo.val ≤ hi.val) :
    (pattern (JuliaLean.base.int.subWrap hi lo) : Int) = hi.val - lo.val := by
  have hlo := lo.property
  have hhi := hi.property
  have he := wrapInt_emod_self t (hi.val - lo.val)
  unfold pattern
  rw [JuliaLean.base.int.subWrap, sub_int_val]
  rw [he]
  have hmod : (hi.val - lo.val) % ((2 ^ t.bits : Nat) : Int) = hi.val - lo.val := by
    apply Int.emod_eq_of_lt (by omega)
    cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hlo hhi ⊢ <;> omega
  rw [hmod]
  exact Int.toNat_of_nonneg (by omega)

private theorem midpoint_half_fits {t : IntTy} (lo hi : JInt t) (h : lo.val ≤ hi.val) :
    t.min ≤ (hi.val - lo.val) / 2 ∧ (hi.val - lo.val) / 2 ≤ t.max := by
  have hlo := lo.property
  have hhi := hi.property
  cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hlo hhi ⊢ <;> omega

/-- Midpoints lie between ordered integer endpoints and round their average down,
    including when the subtraction overflows the signed representation. -/
def BitIntegerMidpointSpec : Prop :=
  ∀ (t : IntTy) (lo hi : JInt t), lo.val ≤ hi.val →
    let mid := midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned lo hi
    mid.val = (lo.val + hi.val) / 2 ∧ lo.val ≤ mid.val ∧ mid.val ≤ hi.val

theorem bitIntegerMidpointSpec : BitIntegerMidpointSpec := by
  intro t lo hi h
  dsimp only
  unfold midpoint
  have hc : pattern (JInt.wrap .u8 1) = 1 := by
    simp [pattern, JInt.wrap, wrapInt, IntTy.bits, IntTy.signed]
  have hs : (JuliaLean.base.int.lshr_BitInteger_BitUnsigned
      (JuliaLean.base.int.subWrap hi lo) (JInt.wrap .u8 1)).val = (hi.val - lo.val) / 2 := by
    rw [JuliaLean.base.int.lshr_BitInteger_BitUnsigned, lshr_int_val,
      midpoint_difference_pattern lo hi h, hc]
    simp only [Int.pow_one]
    exact wrapInt_of_inRange t _ (midpoint_half_fits lo hi h)
  change (JuliaLean.base.int.addWrap lo _).val = _ ∧ _
  rw [JuliaLean.base.int.addWrap, add_int_val, hs]
  have hlo := lo.property
  have hhi := hi.property
  have hf : t.min ≤ lo.val + (hi.val - lo.val) / 2 ∧
      lo.val + (hi.val - lo.val) / 2 ≤ t.max := by omega
  rw [wrapInt_of_inRange t _ hf]
  omega

end

private def byteLexCompare : List (JInt .u8) → List (JInt .u8) → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    if x.val < y.val then -1 else if y.val < x.val then 1 else byteLexCompare xs ys

private def bytePrefixCompare : List (JInt .u8) → List (JInt .u8) → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x.val < y.val then -1 else if y.val < x.val then 1 else bytePrefixCompare xs ys

private def byteLengthCompare (xs ys : List (JInt .u8)) : Int :=
  if xs.length < ys.length then -1 else if ys.length < xs.length then 1 else 0

private theorem bytePrefixCompare_cases (xs ys : List (JInt .u8)) :
    bytePrefixCompare xs ys = -1 ∨ bytePrefixCompare xs ys = 0 ∨ bytePrefixCompare xs ys = 1 := by
  induction xs generalizing ys with
  | nil => simp [bytePrefixCompare]
  | cons x xs ih =>
    cases ys with
    | nil => simp [bytePrefixCompare]
    | cons y ys =>
      simp only [bytePrefixCompare]
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr (Or.inr rfl)
        · exact ih ys

private theorem byte_compare_decompose (xs ys : List (JInt .u8)) :
    (if bytePrefixCompare xs ys < 0 then -1 else
      if bytePrefixCompare xs ys > 0 then 1 else byteLengthCompare xs ys) = byteLexCompare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [bytePrefixCompare, byteLexCompare, byteLengthCompare]
  | cons x xs ih =>
    cases ys with
    | nil => simp [bytePrefixCompare, byteLexCompare, byteLengthCompare]
    | cons y ys =>
      by_cases hxy : x.val < y.val
      · simp [bytePrefixCompare, byteLexCompare, hxy]
      · by_cases hyx : y.val < x.val
        · simp [bytePrefixCompare, byteLexCompare, hxy, hyx]
        · simpa [bytePrefixCompare, byteLexCompare, byteLengthCompare, hxy, hyx] using ih ys

/-- Byte-array comparison follows lexicographic byte order, with a shorter equal-prefix array first. -/
def ByteArrayComparisonSpec : Prop :=
  ∀ (memcmp : List (JInt .u8) → List (JInt .u8) → I → JInt .i32),
    (∀ xs ys, xs.length < 2 ^ 63 → ys.length < 2 ^ 63 →
      ((memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val < 0 ↔
        bytePrefixCompare xs ys = -1) ∧
      ((memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val > 0 ↔
        bytePrefixCompare xs ys = 1)) →
    ∀ xs ys : List (JInt .u8), xs.length < 2 ^ 63 → ys.length < 2 ^ 63 →
      cmpBytes (m := Id) id (fun _ => ()) id
        (fun a => JInt.wrap .i64 a.length) memcmp (fun _ => ())
        (fun a b => JInt.wrap .i64 (JuliaLean.base.operators.cmpInteger
          (fun x y : I => decide (x.val < y.val))
          (fun x y : I => decide (x.val < y.val)) a b)) xs ys =
        JInt.wrap .i64 (byteLexCompare xs ys)

theorem byteArrayComparisonSpec : ByteArrayComparisonSpec := by
  intro memcmp hmem xs ys hxs hys
  have hx := collectorLengthFits _ hxs
  have hy := collectorLengthFits _ hys
  have hm := hmem xs ys hxs hys
  have hd := byte_compare_decompose xs ys
  have hn : ((memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val < 0 ↔
      bytePrefixCompare xs ys < 0) := by
    rcases bytePrefixCompare_cases xs ys with h | h | h <;> simp [h] at hm ⊢ <;> omega
  have hp : ((memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val > 0 ↔
      bytePrefixCompare xs ys > 0) := by
    rcases bytePrefixCompare_cases xs ys with h | h | h <;> simp [h] at hm ⊢ <;> omega
  change (if (memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val < 0
    then JInt.wrap .i64 (-1)
    else if (memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val > 0
    then one else JInt.wrap .i64 (JuliaLean.base.operators.cmpInteger
      (fun x y : I => decide (x.val < y.val))
      (fun x y : I => decide (x.val < y.val))
      (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))) = _
  have hc : JuliaLean.base.operators.cmpInteger
      (fun x y : I => decide (x.val < y.val))
      (fun x y : I => decide (x.val < y.val))
      (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length) = byteLengthCompare xs ys := by
    simp only [JuliaLean.base.operators.cmpInteger, hx, hy, Int.ofNat_lt]
    by_cases hxy : xs.length < ys.length <;> by_cases hyx : ys.length < xs.length <;>
      simp [JuliaLean.base.operators.ifelseValue, byteLengthCompare, hxy, hyx]
  simp only [hn, hp, hc]
  split
  · rename_i hneg
    simpa only [if_pos hneg] using congrArg (JInt.wrap .i64) hd
  · rename_i hneg
    split
    · rename_i hpos
      simpa only [if_neg hneg, if_pos hpos, one] using congrArg (JInt.wrap .i64) hd
    · rename_i hpos
      simpa only [if_neg hneg, if_neg hpos] using congrArg (JInt.wrap .i64) hd


def entries : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-cmp-bytes", juliaFile := "base/array.jl",
    juliaFns := ["cmp(a::Array{UInt8,1}, b::Array{UInt8,1})"],
    statement := "Byte arrays compare lexicographically, with a shorter equal-prefix array first, and return exactly -1, 0 or 1.",
    source := "base/array.jl:2156-2167; lexicographic comparison and native memcmp sign contract",
    status := .proven, prop := ``ByteArrayComparisonSpec, thm := some ``byteArrayComparisonSpec },
  { id := "multidimcov-array-v2-midpoint", juliaFile := "base/array.jl",
    juliaFns := ["midpoint(lo::T, hi::T) where T<:Integer"],
    statement := "For every machine integer width and signedness, the midpoint of ordered endpoints rounds their average down and lies between them, even when their difference overflows.",
    source := "base/array.jl:2281-2283; overflow-safe midpoint contract",
    status := .proven, prop := ``BitIntegerMidpointSpec, thm := some ``bitIntegerMidpointSpec },
  { id := "array-search-boolean-positions", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(A::AbstractArray{Bool})", "findlast(A::AbstractArray{Bool})"],
    statement := "Boolean first and last searches select a true value at the first or last matching position and return nothing exactly when every element is false.",
    source := "base/array.jl:2436; 2624; first and last matching-key contract",
    status := .proven, prop := ``BooleanSearchPositionsSpec, thm := some ``booleanSearchPositionsSpec },
  { id := "array-search-last-complete", juliaFile := "base/array.jl",
    juliaFns := ["findlast(testf::Function, A)"],
    statement := "Last search returns nothing exactly when every iterated value fails the predicate.",
    source := "base/array.jl:2711-2717; findlast matching-key contract",
    status := .proven, prop := ``LastSearchComplete, thm := some ``lastSearchComplete },

  { id := "multidimcov-array-v2-getindex-colon", juliaFile := "base/array.jl",
    juliaFns := ["getindex(A::Array, ::Colon)"],
    statement := "Colon indexing returns a fresh vector with the same element type and every original stored value in linear order, preserving all existing arrays.",
    source := "base/array.jl:995-1002", status := .proven,
    prop := ``ColonArrayCopySpec, thm := some ``colonArrayCopySpec },

  { id := "multidimcov-array-v2-eq-bitint", juliaFile := "base/array.jl",
    juliaFns := ["==(a::Array{<:BitInteger}, b::Array{<:BitInteger})", "==(a::Vector{<:BitInteger}, b::Vector{<:BitInteger})"],
    statement := "Native integer arrays are equal exactly when their shapes and stored values agree; native integer vectors are equal exactly when their stored values agree.",
    source := "base/array.jl:2171-2201; native integer storage has no padding and memcmp compares the requested bytes",
    status := .proven, prop := ``BitIntegerEqualitySpec, thm := some ``bitIntegerEqualitySpec },
  { id := "array-findall-scalar", juliaFile := "base/array.jl",
    juliaFns := ["findall(x::Bool)", "findall(f::Function, x::Number)", "findall(Fix2{typeof(in)}, x::Number)"],
    statement := "A scalar search returns exactly the matching scalar's key, once, and returns no keys when the scalar does not match.",
    source := "base/array.jl:2851-2853; findall matching-key contract",
    status := .proven, prop := ``ScalarFindallSpec, thm := some ``scalarFindallSpec },
  { id := "array-search-oneto-first", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(equalto, r::OneTo)", "findfirst(iszero, r::OneTo)", "findfirst(isone, r::OneTo)"],
    statement := "Searching a one-based integer interval returns the queried key exactly when the key lies in the interval; zero never matches, and one matches precisely a nonempty interval.",
    source := "base/array.jl:2529-2533; findfirst matching-key contract",
    status := .proven, prop := ``OneToFirstSearchSpec, thm := some ``oneToFirstSearchSpec },
  { id := "array-reverseind-wide-index", juliaFile := "base/array.jl",
    juliaFns := ["reverseind(v, i)"],
    statement := "Reversing any valid integer index reflects it through the array's first and last linear indices, including an index wider than the native machine integer.",
    source := "base/array.jl:2276; reverseind index correspondence contract",
    status := .refuted, prop := ``ReverseIndexReflectionSpec,
    thm := some ``reverseIndexReflectionSpec_refuted,
    notes := "For a valid AbstractVector with typemax(Int) elements and Int128(1) as the index, the native firstindex + lastindex sum overflows before subtraction promotes to Int128, producing -9223372036854775809 instead of 9223372036854775807.",
    issue := "none found (queries: reverseind; reverseind overflow; reverseind Int128; reverseind typemax)" },
  { id := "array-copy-shared-heap", juliaFile := "base/array.jl",
    juliaFns := ["copy(a::Array)"],
    statement := "Copying a valid native array allocates a memory object distinct from every old live object, retains the element type, dimensions and every assigned or unassigned slot, and preserves every existing heap object.",
    source := "base/array.jl:391-399; Core memory allocation, memory-reference copy and array header primitives",
    status := .proven, prop := ``SharedHeapArrayCopySpec,
    thm := some ``sharedHeapArrayCopySpec },
  { id := "multidimcov-range-getindex-unsigned", juliaFile := "base/array.jl",
    juliaFns := ["getindex(v::AbstractRange, i::Integer)"],
    statement := "Scalar indexing of OneTo, UnitRange and StepRange agrees with the ordered range values for every BitInteger index, raises BoundsError outside the range, and rejects Bool indices with ArgumentError.",
    source := "base/array.jl:3219-3225; getindex and AbstractRange indexing contracts",
    status := .refuted, prop := ``ScalarRangeIndexSpec,
    thm := some ``scalarRangeIndexSpec_refuted,
    issue := "none found (queries: range getindex unsigned index; StepRange getindex UInt InexactError)",
    notes := "The actual range.jl bounds and scalar-index arithmetic on (-10:2:-2)[UInt64(1)] produces InexactError when converting an unsigned intermediate to Int64. The original nightly reproducer uses the equivalent normalized range -10:2:-1." },
  { id := "array-range-index-ordinary", juliaFile := "base/array.jl",
    juliaFns := ["getindex(v::AbstractRange, i::Integer)"],
    statement := "For ordinary signed Int indices, the array-file wrapper preserves the external range implementation's documented ordered-element indexing law and exact BoundsError; Bool indices are rejected before that implementation runs.",
    source := "base/array.jl:3219-3225; standard signed-index interface of range.jl",
    status := .proven, prop := ``OrdinaryRangeIndexSpec,
    thm := some ``ordinaryRangeIndexSpec },
  { id := "multidimcov-keepat-undef", juliaFile := "base/array.jl",
    juliaFns := ["keepat!(a::Vector, inds)", "keepat!(a::Vector, m::AbstractVector{Bool})"],
    statement := "Keeping sorted unique in-range indices or an equal-length Boolean mask retains the selected slots in order, including unassigned slots, for every valid vector.",
    source := "base/array.jl:3113-3115,3129,3140-3142,3154; keepat! slot-preservation contract",
    status := .refuted, prop := ``KeepatAssignedStateSpec,
    thm := some ``keepatAssignedStateSpec_refuted,
    issue := "related #54401 and #42065 (queries: keepat! undef; keepat! UndefRefError)",
    notes := "Actual keepat3129 and abstractarray.keepAtIndices read every retained slot before testing whether it moves. Retaining an unmoved unassigned slot raises UndefRefError; the corresponding Boolean method skips that read." },
  { id := "multidimcov-get-tuple-vectors", juliaFile := "base/array.jl",
    juliaFns := ["indcopy(sz::Dims, I::Tuple{Vararg{RangeIndex}})",
      "get!(X::AbstractArray, A::AbstractArray, I::RangeVecIntList, default)"],
    statement := "A tuple of index ranges or integer index vectors accepted by get! produces exactly the in-bounds destination positions and source values, with trailing source dimensions combined for the last index collection.",
    source := "base/array.jl:2976-2986; get!/get signatures base/abstractarray.jl:1664-1672",
    status := .refuted, prop := ``TupleVectorIndcopySpec,
    thm := some ``tupleVectorIndcopySpec_refuted,
    issue := "none found (queries: indcopy; RangeVecIntList; get default tuple of vectors MethodError)",
    notes := "The actual tuple-of-ranges method is instantiated; a tuple containing an index vector has no applicable indcopy method. Core.methodError at that exact dispatch also propagates through actual abstractarray.getIndexList. Direct dispatch and the original get reproducer both confirmed MethodError on the pinned nightly." },
  { id := "array-cartesian-read", juliaFile := "base/array.jl",
    juliaFns := ["getindex(A::Array, i1::Int, i2::Int, I::Int...)"],
    statement := "Cartesian reads return the selected assigned cell without changing memory, raise UndefRefError for an unassigned cell, and report bounds or linear-index errors before any read.",
    source := "base/array.jl:974-978; checked memory-read and Cartesian-index interfaces",
    status := .proven, prop := ``CartesianReadSpec,
    thm := some ``cartesianReadSpec },
  { id := "multidimcov-array-v2-collect-array", juliaFile := "base/array.jl",
    juliaFns := ["collect(A::AbstractArray)", "_collect_indices(::Tuple{}, A)",
      "_collect_indices(indsA::Tuple{Vararg{OneTo}}, A)", "_collect_indices(indsA, A)"],
    statement := "Array collection returns a distinct Array with the source element type and dimensions, one-based axes and source elements in linear order, preserving every old heap object. Empty, OneTo and general offset-axis tuples use their actual source methods and checked Core allocation. Every unassigned source slot causes UndefRefError through the documented AbstractArray copying interfaces.",
    source := "base/array.jl:719-725,773,788-801; collect docstring and AbstractArray copy interfaces",
    status := .proven, prop := ``ArrayCollectionSpec, thm := some ``arrayCollectionSpec },
  { id := "array-collect-known-eltype", juliaFile := "base/array.jl",
    juliaFns := ["collect(itr)", "collect_similar(cont, itr)",
      "_collect(cont, itr, ::HasEltype, isz::Union{HasLength,HasShape})",
      "_collect(cont, itr, ::HasEltype, isz::SizeUnknown)"],
    statement := "For iterators with declared element types, collection preserves element order and element type, uses a vector for unknown or length-only size, and preserves checked shape dimensions for shaped iterators. Native sized allocations preserve the old heap; Integer conversion, invalid dimensions and external shape errors propagate. Unknown-sized collection uses actual mutable push and growth. The public trait routers are instantiated with their actual HasEltype methods; EltypeUnknown remains a separate obligation.",
    source := "base/array.jl:719-725,771,775-786; iterator traits, similar and iterable-copy interfaces",
    status := .proven, prop := ``KnownEltypeCollectionSpec,
    thm := some ``knownEltypeCollectionSpec },
  { id := "array-default-eltype-bound", juliaFile := "base/array.jl",
    juliaFns := ["@default_eltype(itr)"],
    statement := "The default collection element type is a supertype of every yielded value's type, including type-constructor Generators, under the documented inference and promote_typejoin_union upper-bound laws.",
    source := "base/array.jl:817-831; default element-type inference interface",
    status := .proven, prop := ``DefaultEltypeBoundSpec,
    thm := some ``defaultEltypeBoundSpec },
  { id := "array-cartesian-assignment", juliaFile := "base/array.jl",
    juliaFns := ["setindex!(A::Array{T}, x, i1::Int, i2::Int, I::Int...)",
      "_setindex!(A::Array{T}, x::T, i1::Int, i2::Int, I::Int...)"],
    statement := "Cartesian assignment converts before checking bounds, leaves every cell unchanged after a conversion, bounds or index-conversion error, writes the converted value to the selected linear cell, and preserves every other cell. Both converting and typed setters are the actual source definitions with checked memory primitives.",
    source := "base/array.jl:1042-1053; assignment, bounds-checking and memory primitive contracts",
    status := .proven, prop := ``CartesianAssignmentSpec,
    thm := some ``cartesianAssignmentSpec },
  { id := "multidimcov-array-v2-collect-alloc", juliaFile := "base/array.jl",
    juliaFns := ["_array_for(::Type{T}, itr, isz)",
      "_array_for_inner(::Type{T}, ::SizeUnknown, ::Nothing)",
      "_array_for_inner(::Type{T}, ::HasLength, len::Integer)",
      "_array_for_inner(::Type{T}, ::HasShape{N}, axs)",
      "_similar_shape(itr, ::HasLength)", "_similar_shape(itr, ::HasShape)",
      "_similar_for(c, ::Type{T}, itr, isz, shp)",
      "_similar_for(c::AbstractArray, ::Type{T}, itr, ::SizeUnknown, ::Nothing)",
      "_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasLength, len::Integer)",
      "_similar_for(c::AbstractArray, ::Type{T}, itr, ::HasShape, axs)"],
    statement := "The collection allocators return distinct requested-type arrays with unassigned storage, preserving old heap objects. Unknown size requests an empty vector, checked HasLength allocation retains the Integer length, and HasShape allocation retains the checked axis lengths, including rank zero. Negative or overflowing dimensions and conversion errors propagate. Native Array-prototype similar routes use actual similar419 and abstractarray shape/varargs methods; the generic non-AbstractArray prototype route retains its documented similar(c,T) size.",
    source := "base/array.jl:696-716; allocation comments, similar interface and Core dimension checks",
    status := .proven, prop := ``CompleteIteratorAllocatorsSpec,
    thm := some ``completeIteratorAllocatorsSpec },
  { id := "multidimcov-array-v2-collect-typed", juliaFile := "base/array.jl",
    juliaFns := ["collect(::Type{T}, itr)",
      "_collect(::Type{T}, itr, isz::Union{HasLength,HasShape})",
      "_collect(::Type{T}, itr, isz::SizeUnknown)"],
    statement := "Typed collection returns a distinct requested-type array containing converted iterator items in order, preserves the declared HasShape dimensions, and uses a vector for HasLength or SizeUnknown. Sized successes preserve existing heap objects; conversion and shape errors propagate, invalid dimensions are rejected before copying, and HasLength is checked through Int conversion. Sized iteration uses the documented equal-size iterable-copy interface; shape conversion uses the documented to_shape interface with actual similarStorageOneTo/similarStorageDims. Unknown-size iteration uses actual mutable push/growth, and concrete integer instances use Base.convert for every source, target and length width.",
    source := "base/array.jl:669-713; typed collect docstring, iterator size/shape invariants, iterable-copy and to_shape interfaces",
    status := .proven, prop := ``CompleteTypedCollectSpec,
    thm := some ``completeTypedCollectSpec },
  { id := "array-similar-unknown-allocation", juliaFile := "base/array.jl",
    juliaFns := ["_similar_for(c::AbstractArray, ::Type{T}, itr, ::SizeUnknown, ::Nothing)"],
    statement := "Unknown-size AbstractArray collection requests the selected similar implementation's zero-length vector of the requested element type. Under the documented similar allocation interface the result has a distinct handle, dimensions (0,), no slots, and leaves every old heap object unchanged. The native Array instance uses actual similarTypeVarargs and similar419 with the signed-dimension Core allocator.",
    source := "base/array.jl:703-704; similar interface and actual AbstractArray varargs/Array similar methods",
    status := .proven, prop := ``CompleteUnknownSimilarSpec,
    thm := some ``completeUnknownSimilarSpec },
  { id := "array-collect-unknown", juliaFile := "base/array.jl",
    juliaFns := ["_collect(::Type{T}, itr, isz::SizeUnknown)"],
    statement := "Unknown-size collection allocates a distinct empty vector, appends every checked converted iterator element in order, preserves the vector's valid storage window through both spare-capacity writes and memory relocation, and returns the first conversion error when conversion fails. The properties cover every source and destination element type through the conversion interface, with concrete Base.convert instances for all BitInteger source and target widths.",
    source := "base/array.jl:688-694; collect docstring and actual push1361/growend/growendInternal over MutableMemory",
    status := .proven, prop := ``CompleteUnknownCollectionSpec,
    thm := some ``completeUnknownCollectionSpec },
  { id := "array-iterator-allocation", juliaFile := "base/array.jl",
    juliaFns := ["_array_for_inner(::Type{T}, ::SizeUnknown, ::Nothing)",
      "_array_for_inner(::Type{T}, ::HasLength, ::Integer)"],
    statement := "Unknown-size collection allocates a fresh empty vector; a known Integer length is checked through Int conversion before allocation, produces a distinct same-type vector with exactly that length and uninitialized storage, preserves every existing heap object, and raises InexactError or ArgumentError for out-of-range or negative lengths, respectively. The integer-conversion instance uses Base.convert for every BitInteger width.",
    source := "base/array.jl:711-712; Core vector allocation and Integer-to-Int conversion contracts",
    status := .proven, prop := ``CompleteCollectorAllocationSpec,
    thm := some ``completeCollectorAllocationSpec },
  { id := "multidimcov-array-v2-convert-array", juliaFile := "base/array.jl",
    juliaFns := ["convert(::Type{T}, ::AbstractArray) where T<:Array"],
    statement := "Conversion returns the identical handle and leaves the whole shared heap unchanged when the source already has the target type; otherwise it allocates a fresh same-shape array containing the converted slots, preserves every old heap entry and propagates conversion or axes errors.",
    source := "base/array.jl:657,664; convert identity and constructor contracts", status := .proven,
    prop := ``CompleteHeapArrayConvertSpec, thm := some ``completeHeapArrayConvertSpec },
  { id := "multidimcov-array-v2-array-constructor", juliaFile := "base/array.jl",
    juliaFns := ["Array{T,N}(::AbstractArray{S,N})"],
    statement := "Array construction returns a distinct heap handle with the requested element type, source dimensions and converted source slots, leaves every existing heap object unchanged, propagates conversion failures, and rejects incompatible non-one-based axes with DimensionMismatch.",
    source := "base/array.jl:663-664; source-mirrored shared-heap copying and abstractarray axes interface",
    status := .proven, prop := ``CompleteHeapArrayConstructorSpec,
    thm := some ``completeHeapArrayConstructorSpec },
  { id := "multidimcov-array-v2-abstractarray-constructor", juliaFile := "base/array.jl",
    juliaFns := ["AbstractArray{T,N}(::AbstractArray{S,N})"],
    statement := "AbstractArray construction allocates a fresh same-size array with the requested type and converted slots, preserves all old shared-heap objects, and propagates allocation, conversion and axes failures, for both ordinary Arrays and generic AbstractArray implementations.",
    source := "base/array.jl:665; actual similar419 for Array inputs; generic similar and copy interfaces from abstractarray.jl",
    status := .proven, prop := ``CompleteHeapAbstractConstructorSpec,
    thm := some ``completeHeapAbstractConstructorSpec },
  { id := "multidimcov-array-v2-zeros-ones", juliaFile := "base/array.jl",
    juliaFns := ["zeros(dims...)", "ones(dims...)", "zeros(::Type, dims...)", "ones(::Type, dims...)",
      "$fname@633", "$fname@634", "$fname@635", "$fname@636", "$fname@637", "$fname@642", "$fname@647"],
    statement := "Constant arrays retain the requested element type, or the selected default Float64 type, and every Integer or OneTo dimension; every slot contains zero(T) or one(T). Rank-zero arrays, negative or non-Int dimensions, unsupported range axes, and allocation or element-construction failures follow their documented interfaces.",
    source := "base/array.jl:589-651; zero/one, allocation, eachindex and generic similar interfaces",
    status := .proven, prop := ``CompleteConstantArraySpec, thm := some ``completeConstantArraySpec },
  { id := "multidimcov-array-v2-fill-dims", juliaFile := "base/array.jl",
    juliaFns := ["fill(v, dims::DimOrInd...)", "fill(v, ::NTuple{N,Union{Integer,OneTo}})",
      "fill(v, ::NTuple{N,Integer})", "fill(v, ::NTuple{N,DimOrInd})", "fill(v, ::Tuple{})"],
    statement := "Fill constructors preserve every requested Integer or OneTo length and put the supplied value in every element, including rank-zero arrays; checked dimension errors propagate before filling and unsupported non-OneTo range axes raise MethodError.",
    source := "base/array.jl:485-587; documented Array allocation, eachindex and generic similar interfaces",
    status := .proven, prop := ``CompleteFillDimensionsSpec, thm := some ``completeFillDimensionsSpec },
  { id := "multidimcov-array-v2-fill-bytes", juliaFile := "base/array.jl",
    juliaFns := ["fill!(::Union{Array{UInt8},Array{Int8}}, ::Integer)"],
    statement := "Byte filling writes precisely the array's slots, returns the same array, preserves every outside byte, and propagates element conversion failures before any write.",
    source := "base/array.jl:473-480; fill! docstring; memset interface", status := .proven,
    prop := ``ByteFillSpec, thm := some ``byteFillSpec },
  { id := "arrayops-copyto-alias", juliaFile := "base/array.jl",
    juliaFns := ["copyto!(::Array, ::Integer, ::Array, ::Integer, ::Integer)",
      "copyto!(::Array, ::Integer, ::Memory, ::Integer, ::Integer)",
      "copyto!(::Memory, ::Integer, ::Array, ::Integer, ::Integer)",
      "copyto!(::Array{T}, ::Integer, ::Array{T}, ::Integer, ::Integer)", "_copyto_impl!"],
    statement := "Checked copies use the pre-call source slots even under arbitrary overlap, preserve every other slot and the destination shape, return the destination, skip all checks for zero counts, and reject negative counts or invalid windows before mutation, for arbitrary Integer offsets and counts.",
    source := "base/array.jl:288-315; copyto! docstring and memory.jl snapshot-copy interface",
    status := .proven, prop := ``CompleteCheckedCopySpec, thm := some ``completeCheckedCopySpec },
  { id := "array-copyto-whole", juliaFile := "base/array.jl",
    juliaFns := ["_copyto2arg!", "copyto!(::Array, ::Array)", "copyto!(::Array, ::Memory)",
      "copyto!(::Memory, ::Array)", "copyto!(::Array{T}, ::Array{T})",
      "copyto!(::Array{T}, ::Memory{T})", "copyto!(::Memory{T}, ::Array{T})"],
    statement := "Whole-source copies replace exactly the destination prefix with the old source, including overlap and unassigned slots, preserve the destination suffix, and reject a longer source without mutation.",
    source := "base/array.jl:323-332; copyto! docstring", status := .proven,
    prop := ``WholeCopySpec, thm := some ``wholeCopySpec },
  { id := "multidimcov-array-v2-fill", juliaFile := "base/array.jl",
    juliaFns := ["fill!(::AbstractArray{T}, x)", "_fill!(::AbstractArray{T}, ::T)"],
    statement := "Filling assigns every slot to the converted value, preserves slots outside the array and the array handle, and propagates conversion errors before mutation.",
    source := "base/array.jl:368-378; fill! docstring", status := .proven,
    prop := ``CompleteFillSpec, thm := some ``completeFillSpec },
  { id := "multidimcov-array-v2-copy", juliaFile := "base/array.jl",
    juliaFns := ["copy(::Array)"],
    statement := "Copying allocates disjoint storage with the same dimensions and the same assigned or unassigned slots, without modifying the source or any existing memory.",
    source := "base/array.jl:391-399; copy docstring; memory allocation and snapshot-copy interfaces",
    status := .proven, prop := ``CopyArraySpec, thm := some ``copyArraySpec },
  { id := "array-take-fields", juliaFile := "base/array.jl",
    juliaFns := ["_take!(::Array{T,N}, ::Array{T,N})"],
    statement := "Taking an array replaces exactly the destination object's memory reference and dimensions with the source object's, preserves every other object, and handles identical source and destination.",
    source := "base/array.jl:402-410; ownership-transfer invariant", status := .proven,
    prop := ``TakeFieldsSpec, thm := some ``takeFieldsSpec },
  { id := "multidimcov-array-v2-similar", juliaFile := "base/array.jl",
    juliaFns := ["similar(::Vector{T})", "similar(::Matrix{T})", "similar(::Vector{T}, ::Type)",
      "similar(::Matrix{T}, ::Type)", "similar(::Array{T}, ::Int)",
      "similar(::Array, ::Type, ::Dims)", "similar(::Array{T}, ::Dims)",
      "similar(::Type{Array{T,N}}, ::Dims)"],
    statement := "Similar arrays have exactly the requested or inherited dimensions, the requested element type and unassigned slots; negative requested dimensions propagate ArgumentError.",
    source := "base/array.jl:414-421; similar docstring and Array allocation interface",
    status := .proven, prop := ``SimilarShapeSpec, thm := some ``similarShapeSpec },
  { id := "array-unsafe-copy-window", juliaFile := "base/array.jl",
    juliaFns := ["unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)"],
    statement := "Valid array windows copy their old source slots, including unassigned references and overlap, preserve all slots outside the destination, and return the destination; zero-length copies touch no memory even with invalid offsets.",
    source := "base/array.jl:266-280; memoryref and memory copy interfaces", status := .proven,
    prop := ``UnsafeArrayCopySpec, thm := some ``unsafeArrayCopySpec },
  { id := "multidimcov-array-v2-safeindex", juliaFile := "base/array.jl",
    juliaFns := ["_safeindex(ex)", "@_safeindex(ex)"],
    statement := "Undoing safe indexed calls restores every ordinary input expression, the macro escapes the restored result, and the rewrite preserves indexed operation counts.",
    source := "base/array.jl:123-156", status := .proven,
    prop := ``SafeindexComplete, thm := some ``safeindexComplete },
  { id := "array-empty-literal", juliaFile := "base/array.jl",
    juliaFns := ["vect()", "getindex(::Type{Any})"],
    statement := "Empty vector literals allocate zero slots.",
    source := "base/array.jl:158,471", status := .proven,
    prop := ``EmptyLiteralSpec, thm := some ``emptyLiteralSpec },
  { id := "multidimcov-array-v2-vect-typed", juliaFile := "base/array.jl",
    juliaFns := ["vect(X::T...)", "getindex(::Type{Any}, vals...)"],
    statement := "Homogeneous vector literals contain exactly their arguments in order, including empty inputs.",
    source := "base/array.jl:158-186,445-471", status := .proven,
    prop := ``LiteralContents, thm := some ``literalContents },
  { id := "multidimcov-array-v2-typed-literal", juliaFile := "base/array.jl",
    juliaFns := ["getindex(::Type{T}, vals...)", "getindex(::Type{Any}, vals...)"],
    statement := "Typed literals preserve the allocated element type and contain each converted value in order; the first failed conversion propagates, for homogeneous and mixed arguments.",
    source := "base/array.jl:445-470", status := .proven,
    prop := ``AllLiteralContents, thm := some ``allLiteralContents },
  { id := "multidimcov-array-v2-vect-promote", juliaFile := "base/array.jl",
    juliaFns := ["vect(X...)"],
    statement := "Mixed vector literals have the promoted element type and the arguments converted to that type in order; conversion errors propagate.",
    source := "base/array.jl:168-186", status := .proven,
    prop := ``PromotedLiteralContents, thm := some ``promotedLiteralContents },
  { id := "multidimcov-array-v2-asize-from", juliaFile := "base/array.jl",
    juliaFns := ["asize_from(a::Array, n)"],
    statement := "Dimension suffixes return size(a)[n:end] for positive Integer n, BoundsError for representable nonpositive n, and InexactError below typemin(Int).",
    source := "base/array.jl:188; size interface from essentials.jl", status := .proven,
    prop := ``DimensionSuffixSpec, thm := some ``dimensionSuffixSpec },
  { id := "multidimcov-array-v2-linear-access", juliaFile := "base/array.jl",
    juliaFns := ["unsetindex!(::Array, ::Int)", "isassigned(::Vector, ::Int)",
      "setindex!(::Array{T}, x, ::Int)", "_setindex!(::Array{T}, ::T, ::Int)"],
    statement := "Checked linear stores round-trip through reads, preserve other slots and shape, reject exactly out-of-range positions, propagate conversion failures without mutation, and unsetting makes only the selected slot unassigned.",
    source := "base/array.jl:209-244,1031-1041; isassigned docstring", status := .proven,
    prop := ``LinearAccessComplete, thm := some ``linearAccessComplete },
  { id := "multidimcov-array-v2-isassigned-linear", juliaFile := "base/array.jl",
    juliaFns := ["isassigned(::Array, ::Int...)"],
    statement := "One index tests linear assignment in 1:length(a); no indices test element one exactly when every dimension has size one.",
    source := "base/array.jl:231-237; documented bounds and sub2ind interfaces", status := .proven,
    prop := ``AssignmentLinearArraySpec, thm := some ``assignmentLinearArraySpec },
  { id := "multidimcov-array-v2-unsetindex-integer", juliaFile := "base/array.jl",
    juliaFns := ["unsetindex!(::Array, ::Integer)"],
    statement := "Integer unsetting rejects Bool and out-of-Int values before mutation, then unsets precisely one in-bounds slot or throws BoundsError without mutation.",
    source := "base/array.jl:208-214; to_index interface", status := .proven,
    prop := ``UnsetIntegerFullSpec, thm := some ``unsetIntegerFullSpec },
  { id := "multidimcov-array-v2-safe-setindex", juliaFile := "base/array.jl",
    juliaFns := ["__safe_setindex!(::Vector{Any}, x, ::Int)",
      "__safe_setindex!(::Vector{T}, ::T, ::Int)", "__safe_setindex!(::Vector{T}, x, ::Int)"],
    statement := "Unchecked literal stores assign precisely the requested slot; a failed element conversion leaves memory unchanged.",
    source := "base/array.jl:1055-1060", status := .proven,
    prop := ``SafeStoreSpec, thm := some ``safeStoreSpec },
  { id := "multidimcov-array-v2-elsize-sizeof", juliaFile := "base/array.jl",
    juliaFns := ["elsize(::Type{A}) where {T,A<:Array{T}}", "elsize(::Type{Ptr{T}})",
      "elsize(::Type{Union{}})", "elsize(::Type{Union{}}, slurp...)", "sizeof(::Array)"],
    statement := "Inline element strides equal their runtime sizes, boxed arrays use pointer strides, sizeof counts element bytes, pointer strides respect alignment, and bottom-type queries return zero or MethodError for extra arguments.",
    source := "base/array.jl:218-229; runtime layout interface", status := .proven,
    prop := ``StorageSizesSpec, thm := some ``storageSizesSpec },
  { id := "multidimcov-array-v2-unsafe-copyto-ptr", juliaFile := "base/array.jl",
    juliaFns := ["unsafe_copyto!(::Ptr{T}, ::Ptr{T}, n)"],
    statement := "Pointer copying returns the destination and copies all bytes of every element from the pre-call source, including overlap, while preserving other bytes.",
    source := "base/array.jl:249-264; memmove interface", status := .proven,
    prop := ``PointerCopySpec, thm := some ``pointerCopySpec },
  { id := "multidimcov-array-v2-empty-concat", juliaFile := "base/array.jl",
    juliaFns := ["DimensionMismatch()", "vcat()", "hcat()"],
    statement := "DimensionMismatch() has an empty message; empty vcat and hcat allocate a zero-length Vector{Any} with no readable index.",
    source := "base/array.jl:14,2332-2333", status := .proven,
    prop := ``EmptyConcatSpec, thm := some ``emptyConcatSpec },
  { id := "tuples-findall-in-isequal", juliaFile := "base/array.jl",
    juliaFns := ["findall(pred::Fix2{typeof(in)}, x::Tuple)"],
    statement := "Specialised tuple membership search agrees with applying membership to each element, including signed zeros and NaNs.",
    source := "base/array.jl:2759-2767 (findall docstring),2962", status := .refuted,
    prop := ``TupleMembershipAgreement, thm := some ``tupleMembershipAgreement_refuted,
    issue := "Related: #29124, #52639 (existing searches: findall in isequal, findall signed zero)",
    notes := "Set construction uses fpiseq; findall(in([0.0]), (-0.0,)) is empty while predicate membership returns [1]." },
  { id := "arrayops-deleteat-range-overflow", juliaFile := "base/array.jl",
    juliaFns := ["deleteat!(::Vector, ::AbstractUnitRange{<:Integer})"],
    statement := "Range deletion removes an in-bounds window, ignores an empty range, and otherwise throws BoundsError without changing the vector, for every integer endpoint type.",
    source := "base/array.jl:1871-1892 (deleteat! docstring),1900-1909", status := .refuted,
    prop := ``DeleteatRangeSpec, thm := some ``deleteatRangeSpec_refuted,
    issue := "Related: #22055 (existing searches: deleteat overflow, deleteat typemax)",
    notes := "The original 1:typemax(Int) case is fixed. For -1:typemax(Int), the negative wrapped length produces ArgumentError instead of BoundsError." },
  { id := "arrayops-deleteat-error-partial", juliaFile := "base/array.jl",
    juliaFns := ["_deleteat!(a::Vector, inds, dltd)"],
    statement := "A deletion rejected for invalid indices leaves the original vector unchanged.",
    source := "Invariant: argument validation errors leave the argument untouched; base/array.jl:1911-1938 (docstring)", status := .refuted,
    prop := ``DeleteatErrorUnchanged, thm := some ``deleteatErrorUnchanged_refuted,
    issue := "Related: #7642, #54401 (existing searches: deleteat error state, deleteat partially modified)",
    notes := "Deleting indices [1,3,5] from [10,20,30,40] throws after overwriting the first slot with 20." },
  { id := "arrayops-splice-convert-undef", juliaFile := "base/array.jl",
    juliaFns := ["splice!(::Vector, ::AbstractUnitRange{<:Integer}, ins)"],
    statement := "A failed splice of a fully assigned vector leaves every slot assigned, including when replacement conversion throws.",
    source := "Invariant: conversion errors do not expose unassigned slots; base/array.jl:1353-1360 (convert-before-growth rationale)", status := .refuted,
    prop := ``SpliceErrorAssigned, thm := some ``spliceErrorAssigned_refuted,
    issue := "Duplicate: #7642; related: #46399, #47112 (existing searches: splice convert error, splice undef)",
    notes := "Inserting Any[\"x\",1] into a String vector at 2:1 grows before conversion and leaves the third slot unassigned." },
  { id := "arrayops-append-many-self", juliaFile := "base/array.jl",
    juliaFns := ["append!(a::AbstractVector, iter...)", "prepend!(a::AbstractVector, iter...)"],
    statement := "Variadic append and prepend concatenate the input collections' values before the call, including repeated aliases of the destination.",
    source := "base/array.jl:1393-1418,1457-1476 (docstrings)", status := .refuted,
    prop := ``AppendManySnapshot, thm := some ``appendManySnapshot_refuted,
    issue := "none found (existing searches: append aliasing, append itself, append! multiple, prepend aliasing)",
    notes := "Two self sources double the vector twice, producing four copies instead of three." },
  { id := "multidim-findfirst-empty-matrix", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(testf::Function, A::AbstractArray)"],
    statement := "Multidimensional predicate search returns the first matching Cartesian key in column-major order or nothing, without throwing for an empty dimension.",
    source := "base/array.jl:2484-2523 (findfirst docstring),2526-2527", status := .refuted,
    prop := ``FindfirstCartesian, thm := some ``findfirstCartesian_refuted,
    issue := "Duplicate: #36938; related: #40120 (existing searches: findfirst empty matrix, findfirst BoundsError empty)",
    notes := "A 0-by-3 array starts at CartesianIndex(1,1), which passes the last-key test and is read out of bounds." },
  { id := "multidimcov-intersect-range-vector", juliaFile := "base/array.jl",
    juliaFns := ["intersect(v::AbstractVector, r::AbstractRange)", "intersect(r::AbstractRange, v::AbstractVector)"],
    statement := "Vector/range intersection returns the distinct shared elements in the first argument's encounter order.",
    source := "base/abstractset.jl:115-121 (intersect docstring); base/array.jl:3210-3216", status := .refuted,
    prop := ``IntersectRangeVectorOrder, thm := some ``intersectRangeVectorOrder_refuted,
    issue := "none found (existing searches: intersect range vector order, intersect AbstractRange AbstractVector order)",
    notes := "intersect(1:3,[3,2,1]) returns [3,2,1] because the range-first method swaps its arguments." },
  { id := "arraycov-indexin-isequal", juliaFile := "base/array.jl",
    juliaFns := ["indexin(a, b::AbstractArray)"],
    statement := "indexin returns the first index of each value under collection-membership equality.",
    source := "base/array.jl:2861-2868 (indexin docstring),2887-2895", status := .refuted,
    prop := ``IndexinMembershipAgreement, thm := some ``indexinMembershipAgreement_refuted,
    issue := "none found (existing searches: indexin isequal, indexin NaN signed zero, indexin membership)",
    notes := "indexin([-0.0],[0.0]) returns [nothing] although -0.0 is a member of [0.0]." },
  { id := "ranges-operations-findfirst-overflow", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(==(::Integer), ::StepRange)", "findfirst(==(::Integer), ::AbstractUnitRange)"],
    statement := "A matching integer in an integer range returns a positive search index.",
    source := "base/array.jl:2484-2523 (docstring),2535-2547", status := .refuted,
    prop := ``RangeFindfirstPositive, thm := some ``rangeFindfirstPositive_refuted,
    issue := "none found (queries: findfirst StepRange Int8 overflow)",
    notes := "findfirst(==(Int8(100)), Int8(-100):Int8(2):Int8(120)) returns -27." },
  { id := "arrayops-reverse-window-inconsistent", juliaFile := "base/array.jl",
    juliaFns := ["reverse(::AbstractVector, ::Integer, ::Integer)", "reverse!(::AbstractVector, ::Integer, ::Integer)"],
    statement := "reverse and reverse! of a copy agree on contents or exception type for every window.",
    source := "base/array.jl:2291-2293 (docstring),2248-2260,2312-2328", status := .refuted,
    prop := ``ReverseCopyAgrees, thm := some ``reverseCopyAgrees_refuted,
    issue := "none found (queries: reverse reverse! bounds start stop)",
    notes := "For [1,2,3] and window 5:5, reverse throws BoundsError and reverse! returns unchanged." },
  { id := "multidimcov-wrap-negative-length", juliaFile := "base/array.jl",
    juliaFns := ["_wrap(::MemoryRef, ::Dims)",
      "wrap(::Type{Array}, ::MemoryRef, ::Tuple)", "wrap(::Type{Array}, ::Memory, ::Tuple)",
      "wrap(::Type{Array}, ::MemoryRef, ::Integer)", "wrap(::Type{Array}, ::Memory, ::Integer)",
      "wrap(::Type{Array}, ::Memory)"],
    statement := "Wrapping preserves memory and requested nonnegative dimensions, rejects excessive size and negative dimensions, and checks Int conversion.",
    source := "base/array.jl:3228-3231 (docstring),3236-3274", status := .refuted,
    prop := ``WrapDocumented, thm := some ``wrapDocumented_refuted,
    issue := "none found (queries: wrap Memory negative dimensions)",
    notes := "The singleton Core.checked_dims method returns a negative size unchanged, and _wrap accepts it." },
  { id := "arraycov-wrap-memory-unsigned", juliaFile := "base/array.jl",
    juliaFns := ["wrap(::Type{Array}, ::Memory, ::Integer)"],
    statement := "Memory wrapping accepts every nonnegative Int-representable Integer length that fits.",
    source := "base/array.jl:3228-3231 (docstring),3265-3269", status := .refuted,
    prop := ``WrapMemoryIntegerSpec, thm := some ``wrapMemoryIntegerSpec_refuted,
    issue := "none found (queries: wrap Memory unsigned MethodError)",
    notes := "The Memory overload passes the unconverted length to _wrap, whose tuple method requires Int." },
  { id := "arrayops-findnext-start-below", juliaFile := "base/array.jl",
    juliaFns := ["findnext(predicate, A, start)", "findprev(predicate, A, start)"],
    statement := "For every start representable as Int, findnext/findprev return the next/previous matching key or nothing.",
    source := "base/array.jl:2442-2481,2630-2677 (docstrings)", status := .refuted,
    prop := ``FindAllStarts, thm := some ``findAllStarts_refuted,
    issue := "none found (queries: findnext start bounds; findprev start bounds)",
    notes := "findnext(iseven, [1,2], 0) raises BoundsError instead of returning 2." },
  { id := "array-isbitsunion-small", juliaFile := "base/array.jl", juliaFns := ["isbitsunion(::Type)"],
    statement := "A union of 2 through 126 well-formed concrete members is isbitsunion exactly when every member is isbitstype.",
    source := "base/array.jl:192-206 (docstring)", status := .proven,
    prop := ``IsBitsUnionSmall, thm := some ``isBitsUnionSmall },
  { id := "array-search-first-sound", juliaFile := "base/array.jl", juliaFns := ["findfirst(predicate, collection)"],
    statement := "A successful forward search returns a key of an element satisfying the predicate.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``FirstSearchSound, thm := some ``firstSearchSound },
  { id := "array-search-first-complete", juliaFile := "base/array.jl", juliaFns := ["findfirst(predicate, collection)"],
    statement := "Forward search returns nothing exactly when no collection element satisfies the predicate.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``FirstSearchComplete, thm := some ``firstSearchComplete },
  { id := "array-search-first-earliest", juliaFile := "base/array.jl", juliaFns := ["findfirst(predicate, collection)"],
    statement := "A successful forward search returns the first matching key in iteration order.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``FirstSearchEarliest, thm := some ``firstSearchEarliest },
  { id := "array-search-last-sound", juliaFile := "base/array.jl", juliaFns := ["findlast(predicate, collection)"],
    statement := "A successful backward search returns a key of an element satisfying the predicate.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``LastSearchSound, thm := some ``lastSearchSound },
  { id := "array-search-last-latest", juliaFile := "base/array.jl", juliaFns := ["findlast(predicate, collection)"],
    statement := "A successful backward search returns the last matching key in iteration order.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``LastSearchLatest, thm := some ``lastSearchLatest },
  { id := "multidimcov-isbitsunion-many-members", juliaFile := "base/array.jl",
    juliaFns := ["isbitsunion(::Type)", "allocatedinline(::Type)"],
    statement := "isbitsunion identifies every union whose members are isbitstype, regardless of member count.",
    source := "base/array.jl:192-206 (docstring)", status := .refuted,
    prop := ``IsBitsUnionDocumented, thm := some ``isBitsUnionDocumented_refuted,
    issue := "none found (queries: isbitsunion 127; isbitsunion members)",
    notes := "A union of 127 distinct singleton Val types has only isbits members and isbitsunion returns false." }
]


end JuliaLean.Proofs.base.array

/-!
Nothing to promise:
_throw_argerror@321: internal exception construction; user-facing error conditions belong to its checking callers.
promote_rule@659: internal type-policy routing through promote_type and el_same, whose promotion policies are defined in promotion.jl and range.jl; this method adds no separate array operation.
_similar_for@697: generic non-AbstractArray container fallback forwards to the container's external similar(c,T) interface; container allocation and content policies belong to that interface.
_similar_shape@699: internal SizeUnknown metadata adapter returns nothing; allocation and content guarantees belong to the collection callers.
_similar_shape@700: internal HasLength metadata adapter forwards the documented Integer-valued length query unchanged; conversion and allocation checks belong to _array_for_inner.
_similar_shape@701: internal HasShape metadata adapter forwards the documented axes query unchanged; allocation and axes support belong to the collection callers.
_similar_for@705: internal HasLength dispatch adapter passes the container, requested element type, and Integer length unchanged to similar; allocation, conversion, and shape guarantees belong to the selected similar method.
_similar_for@707: internal HasShape dispatch adapter passes the requested axes unchanged to similar; axes support and allocation guarantees belong to the selected similar method.
_array_for_inner@713: internal shaped-allocation dispatch adapter forwards the Array type and axes unchanged to similar; it adds no allocation or axes policy of its own.
_array_for@716: internal trait router obtains the iterator's shape descriptor and delegates allocation to _array_for_inner; the shape adapters and selected allocator own the resulting dimensions and errors.
to_dim@482: internal dimension-dispatch adapter that returns an Integer unchanged; allocation and dimension validation belong to its constructor callers.
to_dim@483: internal dimension-dispatch adapter that forwards to OneTo's last; range endpoint semantics belong to range.jl and allocation checks belong to the constructor callers.
invalid_wrap_err@3244: internal exception construction; user-facing error conditions belong to the wrapping callers.
push!(::Nowhere, _)@1944: the internal optional-output sink discards an item and has no separate public operation.
_growend!(::Nowhere, _)@1945: the internal optional-output sink discards a slot request and has no separate public operation.
_iterator_upper_bound@805: inference-only helper; at runtime it throws TypeError (checked on nightly); nothing to promise.
reverse@2268: internal tuple-dimension adapter forwards the sole Integer dimension to the selected reverse method; dimension validation and content behavior belong to that method.
collect_similar@775: internal trait router forwards the container and iterator unchanged to the selected _collect method; it introduces no new allocation, iteration or element-type policy.

Declaration-only rows, with no Julia method body:
fill@581, zeros@608, ones@629, getindex@972, setindex!@1029,
push!@1351, append!@1420, prepend!@1478, sizehint!@1610, wrap@3233.
-/

/-!
## Method-to-property inventory

253 mirrored methods: 147 covered and 106 awaiting a complete property.
Registry: 52 proven and 18 refuted entries.

`NOT DONE` means no complete real property has been settled for that method.
Search proofs currently cover pure predicates on finite ordered pairs; the boundary
refutation uses fully assigned standard vectors. These entries do not claim a proof
for effectful predicates or every custom collection implementation.

DimensionMismatch@14: multidimcov-array-v2-empty-concat
_safeindex@132: multidimcov-array-v2-safeindex
_safeindex@135: multidimcov-array-v2-safeindex
vect@158: array-empty-literal
vect@159: multidimcov-array-v2-vect-typed
vect@183: multidimcov-array-v2-vect-promote
asize_from@188: multidimcov-array-v2-asize-from
allocatedinline@190: multidimcov-isbitsunion-many-members
isbitsunion@206: multidimcov-isbitsunion-many-members, array-isbitsunion-small
unsetindex!@208: multidimcov-array-v2-unsetindex-integer
unsetindex!@209: multidimcov-array-v2-linear-access
elsize@218: multidimcov-array-v2-elsize-sizeof
elsize@219: multidimcov-array-v2-elsize-sizeof
elsize@226: multidimcov-array-v2-elsize-sizeof
elsize@227: multidimcov-array-v2-elsize-sizeof
sizeof@229: multidimcov-array-v2-elsize-sizeof
isassigned@231: multidimcov-array-v2-isassigned-linear
isassigned@239: multidimcov-array-v2-linear-access
unsafe_copyto!@259: multidimcov-array-v2-unsafe-copyto-ptr
unsafe_copyto!@276: array-unsafe-copy-window
copyto!@288: arrayops-copyto-alias
copyto!@290: arrayops-copyto-alias
copyto!@292: arrayops-copyto-alias
copyto!@296: arrayops-copyto-alias
_copyto_impl!@299: arrayops-copyto-alias
_throw_argerror@321: Nothing to promise (internal construction helper)
_copyto2arg!@323: array-copyto-whole
copyto!@325: array-copyto-whole
copyto!@326: array-copyto-whole
copyto!@327: array-copyto-whole
copyto!@330: array-copyto-whole
copyto!@331: array-copyto-whole
copyto!@332: array-copyto-whole
fill!@368: multidimcov-array-v2-fill
_fill!@373: multidimcov-array-v2-fill
copy@391: multidimcov-array-v2-copy, array-copy-shared-heap
_take!@402: array-take-fields
similar@414: multidimcov-array-v2-similar
similar@415: multidimcov-array-v2-similar
similar@416: multidimcov-array-v2-similar
similar@417: multidimcov-array-v2-similar
similar@418: multidimcov-array-v2-similar
similar@419: multidimcov-array-v2-similar
similar@420: multidimcov-array-v2-similar
similar@421: multidimcov-array-v2-similar
getindex@445: multidimcov-array-v2-typed-literal
getindex@463: multidimcov-array-v2-typed-literal
getindex@471: array-empty-literal
fill!@473: multidimcov-array-v2-fill-bytes
to_dim@482: Nothing to promise (internal dimension-dispatch adapter)
to_dim@483: Nothing to promise (internal endpoint forwarding)
fill@581: declaration only
fill@583: multidimcov-array-v2-fill-dims
fill@584: multidimcov-array-v2-fill-dims
fill@585: multidimcov-array-v2-fill-dims
fill@586: multidimcov-array-v2-fill-dims
fill@587: multidimcov-array-v2-fill-dims
zeros@608: declaration only
ones@629: declaration only
$fname@633: multidimcov-array-v2-zeros-ones
$fname@634: multidimcov-array-v2-zeros-ones
$fname@635: multidimcov-array-v2-zeros-ones
$fname@636: multidimcov-array-v2-zeros-ones
$fname@637: multidimcov-array-v2-zeros-ones
$fname@642: multidimcov-array-v2-zeros-ones
$fname@647: multidimcov-array-v2-zeros-ones
convert@657: multidimcov-array-v2-convert-array
promote_rule@659: Nothing to promise (external promotion-policy routing)
Array{T,N}@664: multidimcov-array-v2-array-constructor
AbstractArray{T,N}@665: multidimcov-array-v2-abstractarray-constructor
collect@684: multidimcov-array-v2-collect-typed
_collect@686: multidimcov-array-v2-collect-typed
_collect@688: array-collect-unknown
_similar_for@697: Nothing to promise (external container allocation policy)
_similar_shape@699: Nothing to promise (SizeUnknown metadata adapter)
_similar_shape@700: Nothing to promise (Integer length metadata adapter)
_similar_shape@701: Nothing to promise (axes metadata adapter)
_similar_for@703: array-similar-unknown-allocation
_similar_for@705: Nothing to promise (unchanged length forwarding to similar)
_similar_for@707: Nothing to promise (unchanged axes forwarding to similar)
_array_for_inner@711: array-iterator-allocation
_array_for_inner@712: array-iterator-allocation
_array_for_inner@713: Nothing to promise (shaped similar dispatch)
_array_for@716: Nothing to promise (iterator-trait allocation router)
collect@771: NOT DONE
collect@773: multidimcov-array-v2-collect-array
collect_similar@775: Nothing to promise (internal trait router)
_collect@777: array-collect-known-eltype
_collect@780: array-collect-known-eltype
_collect_indices@788: multidimcov-array-v2-collect-array
_collect_indices@793: multidimcov-array-v2-collect-array
_collect_indices@798: multidimcov-array-v2-collect-array
_iterator_upper_bound@805: Nothing to promise (inference-only helper; runtime non-boolean condition)
default_eltype@821: array-default-eltype-bound
collect@833: NOT DONE
_collect@855: NOT DONE
_collect@858: NOT DONE
collect_to_with_first!@875: NOT DONE
collect_to_with_first!@881: NOT DONE
setindex_widen_up_to@886: NOT DONE
collect_to!@895: NOT DONE
grow_to!@914: NOT DONE
push_widen@922: NOT DONE
grow_to!@935: NOT DONE
getindex@972: declaration only
getindex@974: array-cartesian-read
getindex@981: NOT DONE
getindex@993: NOT DONE
getindex@995: multidimcov-array-v2-getindex-colon
getindex@1005: NOT DONE
setindex!@1029: declaration only
setindex!@1031: multidimcov-array-v2-linear-access
_setindex!@1036: multidimcov-array-v2-linear-access
setindex!@1042: array-cartesian-assignment
_setindex!@1047: array-cartesian-assignment
__safe_setindex!@1055: multidimcov-array-v2-safe-setindex
__safe_setindex!@1057: multidimcov-array-v2-safe-setindex
__safe_setindex!@1059: multidimcov-array-v2-safe-setindex
setindex!@1063: NOT DONE
setindex!@1078: NOT DONE
setindex!@1088: NOT DONE
overallocation@1102: NOT DONE
array_new_memory@1114: NOT DONE
_growbeg_internal!@1116: NOT DONE
_growbeg!@1151: NOT DONE
_growend_internal!@1171: NOT DONE
_growend!@1212: NOT DONE
_growat!@1225: NOT DONE
_deletebeg!@1273: NOT DONE
_deleteend!@1291: NOT DONE
_deleteat!@1307: NOT DONE
push!@1351: declaration only
push!@1353: NOT DONE
_push!@1361: NOT DONE
push!@1368: NOT DONE
push!@1373: NOT DONE
append!@1420: declaration only
append!@1422: NOT DONE
append!@1430: NOT DONE
push!@1431: NOT DONE
append!@1432: arrayops-append-many-self
_append!@1434: NOT DONE
_append!@1442: NOT DONE
prepend!@1478: declaration only
prepend!@1480: NOT DONE
prepend!@1495: NOT DONE
pushfirst!@1496: NOT DONE
prepend!@1497: arrayops-append-many-self
_prepend!@1499: NOT DONE
_prepend!@1512: NOT DONE
resize!@1559: NOT DONE
sizehint!@1610: declaration only
sizehint!@1612: NOT DONE
Core.kwcall@1647: NOT DONE
pop!@1695: NOT DONE
popat!@1736: NOT DONE
popat!@1743: NOT DONE
pushfirst!@1772: NOT DONE
_pushfirst!@1777: NOT DONE
pushfirst!@1784: NOT DONE
pushfirst!@1789: NOT DONE
popfirst!@1831: NOT DONE
insert!@1861: NOT DONE
_insert!@1866: NOT DONE
deleteat!@1894: NOT DONE
deleteat!@1900: arrayops-deleteat-range-overflow
deleteat!@1940: NOT DONE
deleteat!@1941: NOT DONE
push!@1944: Nothing to promise (internal output sink)
_growend!@1945: Nothing to promise (internal output sink)
_push_deleted!@1947: NOT DONE
_copy_item!@1956: NOT DONE
_deleteat!@1965: arrayops-deleteat-error-partial
deleteat!@2000: NOT DONE
splice!@2065: NOT DONE
splice!@2120: arrayops-splice-convert-undef
splice!@2148: NOT DONE
empty!@2150: NOT DONE
cmp@2156: multidimcov-array-v2-cmp-bytes
==@2171: multidimcov-array-v2-eq-bitint
==@2188: multidimcov-array-v2-eq-bitint
reverse@2248: arrayops-reverse-window-inconsistent
$f@2266: NOT DONE
$_f@2267: NOT DONE
$_f@2268: Nothing to promise (internal tuple-dimension adapter)
$_f@2269: NOT DONE
reverseind@2276: array-reverseind-wide-index
midpoint@2283: multidimcov-array-v2-midpoint
midpoint@2284: Nothing to promise (promotes mixed integer endpoints and forwards to the same-type midpoint)
reverse!@2312: arrayops-reverse-window-inconsistent
vcat@2332: multidimcov-array-v2-empty-concat
hcat@2333: multidimcov-array-v2-empty-concat
hcat@2335: NOT DONE
hcat@2344: NOT DONE
vcat@2346: NOT DONE
vcat@2361: NOT DONE
_cat@2363: NOT DONE
findnext@2399: NOT DONE
findfirst@2436: array-search-boolean-positions
findfirst@2439: NOT DONE
findnext@2470: arrayops-findnext-start-below
findfirst@2518: array-search-first-sound, array-search-first-complete, array-search-first-earliest
findfirst@2526: multidim-findfirst-empty-matrix
findfirst@2529: array-search-oneto-first
findfirst@2532: array-search-oneto-first
findfirst@2533: array-search-oneto-first
findfirst@2535: ranges-operations-findfirst-overflow
findfirst@2541: ranges-operations-findfirst-overflow
findfirst@2549: NOT DONE
findfirst@2550: NOT DONE
findprev@2586: NOT DONE
findlast@2624: array-search-boolean-positions
findlast@2627: NOT DONE
findprev@2666: arrayops-findnext-start-below
findlast@2711: array-search-last-sound, array-search-last-latest, array-search-last-complete
findlast@2719: NOT DONE
findlast@2723: NOT DONE
findlast@2728: NOT DONE
findall@2784: NOT DONE
findall@2791: NOT DONE
findall@2833: NOT DONE
findall@2838: NOT DONE
findall@2851: array-findall-scalar
findall@2852: array-findall-scalar
findall@2853: array-findall-scalar
indexin@2887: arraycov-indexin-isequal
_findin@2898: NOT DONE
_findin@2905: NOT DONE
_sortedfindin@2910: NOT DONE
findall@2952: NOT DONE
findall@2961: NOT DONE
findall@2962: tuples-findall-in-isequal
indcopy@2965: NOT DONE
indcopy@2976: multidimcov-get-tuple-vectors
filter@3015: NOT DONE
filter@3027: NOT DONE
filter!@3061: NOT DONE
filter@3100: NOT DONE
keepat!@3129: multidimcov-keepat-undef
keepat!@3154: multidimcov-keepat-undef
_unique_filter!@3159: NOT DONE
_grow_filter!@3169: NOT DONE
_shrink_filter!@3170: NOT DONE
_grow!@3172: NOT DONE
union!@3180: NOT DONE
symdiff!@3183: NOT DONE
_shrink!@3186: NOT DONE
intersect!@3193: NOT DONE
setdiff!@3194: NOT DONE
vectorfilter@3196: NOT DONE
intersect@3198: NOT DONE
setdiff@3204: NOT DONE
intersect@3210: multidimcov-intersect-range-vector
intersect@3216: multidimcov-intersect-range-vector
getindex@3219: multidimcov-range-getindex-unsigned, array-range-index-ordinary
wrap@3233: declaration only
_wrap@3236: multidimcov-wrap-negative-length
invalid_wrap_err@3244: Nothing to promise (internal construction helper)
wrap@3249: multidimcov-wrap-negative-length
wrap@3255: multidimcov-wrap-negative-length
wrap@3260: multidimcov-wrap-negative-length
wrap@3265: multidimcov-wrap-negative-length, arraycov-wrap-memory-unsigned
wrap@3270: multidimcov-wrap-negative-length
-/
