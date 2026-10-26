import JuliaLean.SortTuplesCov.SortTop

/-! Unsigned order-preserving mappings from `base/sort.jl:2227-2310`
(master `bbfa0ce4150`).  A bit integer is its fixed-width bit pattern. -/

namespace JuliaLean.SortTuplesCov

def wordMask (bits : Nat) : Nat := 2 ^ bits - 1
def signMask (bits : Nat) : Nat := 2 ^ (bits - 1)

/-- Unsigned Forward methods, `base/sort.jl:2267-2268`. -/
def uintMapUnsigned (word : Nat) : Nat := word
def uintUnmapUnsigned (word : Nat) : Nat := word

/-- Signed Forward methods, `base/sort.jl:2270-2273`. -/
def uintMapSigned (bits word : Nat) : Nat := word ^^^ signMask bits
def uintUnmapSigned (bits word : Nat) : Nat := word ^^^ signMask bits

/-- Char methods, `base/sort.jl:2282-2284`: reinterpret to and from UInt32. -/
def uintMapChar (code : UInt32) : UInt32 := code
def uintUnmapChar (word : UInt32) : UInt32 := word

/-- ReverseOrdering methods, `base/sort.jl:2287-2289`. -/
def uintMapReverse (bits : Nat) (forward : Nat → Nat) (word : Nat) : Nat :=
  wordMask bits ^^^ forward word
def uintUnmapReverse (bits : Nat) (forwardUnmap : Nat → Nat) (word : Nat) : Nat :=
  forwardUnmap (wordMask bits ^^^ word)

inductive UIntMapType where
  | bits (width : Nat) | char | unsupported
  deriving DecidableEq

/-- `UIntMappable`, including fallback, Forward bit integers and Char, and
ReverseOrdering forwarding, `base/sort.jl:2237,2275,2284,2289`. -/
def uintMappable : UIntMapType → Bool → Option Nat
  | .bits width, _ => some width
  | .char, _ => some 32
  | .unsupported, _ => none

def UIntMappingCorrect : Prop :=
  (∀ x, uintMapUnsigned x = x ∧ uintUnmapUnsigned x = x) ∧
  (∀ bits x, uintUnmapSigned bits (uintMapSigned bits x) = x) ∧
  (∀ c, uintUnmapChar (uintMapChar c) = c) ∧
  (∀ bits f x, uintMapReverse bits f x = wordMask bits ^^^ f x) ∧
  (∀ bits f x, uintUnmapReverse bits f x = f (wordMask bits ^^^ x)) ∧
  (∀ width reverse, uintMappable (.bits width) reverse = some width) ∧
  (∀ reverse, uintMappable .char reverse = some 32) ∧
  (∀ reverse, uintMappable .unsupported reverse = none)

theorem uintMappingCorrect : UIntMappingCorrect := by
  refine ⟨by simp [uintMapUnsigned, uintUnmapUnsigned], ?_,
    by simp [uintMapChar, uintUnmapChar], by simp [uintMapReverse],
    by simp [uintUnmapReverse], by simp [uintMappable], by simp [uintMappable],
    by simp [uintMappable]⟩
  intro bits x
  simp [uintMapSigned, uintUnmapSigned, Nat.xor_assoc]

/-! ### Vector mapping loops -/

def uintMapLoop (map : Nat → Nat) (lo : Int) : Nat → Array Nat → Array Nat
  | 0, v => v
  | fuel + 1, v =>
    let i := lo + fuel
    uintMapLoop map lo fuel (JuliaLean.Sort.wr v i (map (JuliaLean.Sort.rd v i)))

/-- `uint_map!`, `base/sort.jl:2295-2301`. -/
def uintMapBang (map : Nat → Nat) (v : Array Nat) (lo hi : Int) : Array Nat :=
  uintMapLoop map lo (hi - lo + 1).toNat v

def uintUnmapLoop (unmap : Nat → Nat) (offset : Nat) (lo indexOffset : Int) :
    Nat → Array Nat → Array Nat → Array Nat
  | 0, v, _ => v
  | fuel + 1, v, u =>
    let i := lo + fuel
    uintUnmapLoop unmap offset lo indexOffset fuel
      (JuliaLean.Sort.wr v i (unmap (JuliaLean.Sort.rd u (i + indexOffset) + offset))) u

/-- `uint_unmap!`, `base/sort.jl:2303-2310`. -/
def uintUnmapBang (unmap : Nat → Nat) (v u : Array Nat) (lo hi : Int)
    (offset : Nat := 0) (indexOffset : Int := 0) : Array Nat :=
  uintUnmapLoop unmap offset lo indexOffset (hi - lo + 1).toNat v u

def UIntMappingLoopsCorrect : Prop :=
  (∀ map v lo hi, uintMapBang map v lo hi =
    uintMapLoop map lo (hi - lo + 1).toNat v) ∧
  (∀ unmap v u lo hi off io, uintUnmapBang unmap v u lo hi off io =
    uintUnmapLoop unmap off lo io (hi - lo + 1).toNat v u)

theorem uintMappingLoopsCorrect : UIntMappingLoopsCorrect := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-! ### Legacy algorithm wrapping -/

inductive PublicAlg where
  | quick | merge | insertion | other
  deriving DecidableEq

/-- `maybe_apply_initial_optimizations`, `base/sort.jl:2396-2399`. -/
def maybeApplyInitialOptimizations : PublicAlg → Bool
  | .quick | .merge | .insertion => true
  | .other => false

def MaybeApplyInitialOptimizationsCorrect : Prop :=
  ∀ alg, maybeApplyInitialOptimizations alg =
    match alg with
    | .quick | .merge | .insertion => true
    | .other => false

theorem maybeApplyInitialOptimizationsCorrect : MaybeApplyInitialOptimizationsCorrect := by
  intro alg
  cases alg <;> rfl

end JuliaLean.SortTuplesCov
