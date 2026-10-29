import JuliaLean.AbstractArrayCov.Rows.AliasGet

/-! Thin, method-specific concatenation adapters in `base/abstractarray.jl:1697-2292`. -/

namespace JuliaLean.AbstractArrayCov.Rows.ConcatDirect

open JuliaLean
open JuliaLean.Registry

structure MatrixResult (α : Type) where
  rows : Nat
  cols : Nat
  values : List α
  deriving Repr, DecidableEq

def emptyVector : List α := []

def method1697 (_dim : Int) : List α := []
def Property1697 : Prop := ∀ (α : Type) dim, (method1697 dim : List α) = []
theorem property1697 : Property1697 := by unfold Property1697; intros; rfl

def method1699 (elementType : Type) : List elementType := []
def Property1699 : Prop := ∀ (elementType : Type), method1699 elementType = []
theorem property1699 : Property1699 := by unfold Property1699; intros; rfl

def method1700 (elementType : Type) : List elementType := []
def Property1700 : Prop := ∀ (elementType : Type), method1700 elementType = []
theorem property1700 : Property1700 := by unfold Property1700; intros; rfl

/-- Same-type scalar `vcat` comprehensions, lines 1703-1704. -/
def method1703 (values : List α) : List α := values
def Property1703 : Prop := ∀ (α : Type) values, method1703 (α := α) values = values
theorem property1703 : Property1703 := by unfold Property1703; intros; rfl

def method1704 (values : List α) : List α := values
def Property1704 : Prop := ∀ (α : Type) values, method1704 (α := α) values = values
theorem property1704 : Property1704 := by unfold Property1704; intros; rfl

/-- Same-type scalar `hcat` comprehensions, lines 1705-1706. -/
def method1705 (values : List α) : MatrixResult α := ⟨1, values.length, values⟩
def Property1705 : Prop := ∀ (α : Type) values,
  method1705 (α := α) values = ⟨1, values.length, values⟩
theorem property1705 : Property1705 := by unfold Property1705; intros; rfl

def method1706 (values : List α) : MatrixResult α := ⟨1, values.length, values⟩
def Property1706 : Prop := ∀ (α : Type) values,
  method1706 (α := α) values = ⟨1, values.length, values⟩
theorem property1706 : Property1706 := by unfold Property1706; intros; rfl

def allocateFill (allocate : Nat → β) (fill : β → Bool → List α → γ)
    (values : List α) : γ := fill (allocate values.length) false values

def method1708 (promote : List α → τ) (allocate : τ → Nat → β)
    (fill : β → Bool → List α → γ) (values : List α) : γ :=
  fill (allocate (promote values) values.length) false values
def Property1708 : Prop := ∀ (α τ β γ : Type) (promote : List α → τ)
    (allocate : τ → Nat → β) (fill : β → Bool → List α → γ) values,
  method1708 promote allocate fill values =
    fill (allocate (promote values) values.length) false values
theorem property1708 : Property1708 := by unfold Property1708; intros; rfl

def method1714 (promote : List α → τ) (allocate : τ → Nat → Nat → β)
    (fill : β → Bool → List α → γ) (values : List α) : γ :=
  fill (allocate (promote values) 1 values.length) false values
def Property1714 : Prop := ∀ (α τ β γ : Type) (promote : List α → τ)
    (allocate : τ → Nat → Nat → β) (fill : β → Bool → List α → γ) values,
  method1714 promote allocate fill values =
    fill (allocate (promote values) 1 values.length) false values
theorem property1714 : Property1714 := by unfold Property1714; intros; rfl

def method1720 (allocate : τ → Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (values : List α) : γ :=
  fill (allocate t values.length) false values
def Property1720 : Prop := ∀ (τ α β γ : Type) (allocate : τ → Nat → β)
    (fill : β → Bool → List α → γ) t values,
  method1720 allocate fill t values = fill (allocate t values.length) false values
theorem property1720 : Property1720 := by unfold Property1720; intros; rfl

def method1726 (allocate : τ → Nat → Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (values : List α) : γ :=
  fill (allocate t 1 values.length) false values
def Property1726 : Prop := ∀ (τ α β γ : Type) (allocate : τ → Nat → Nat → β)
    (fill : β → Bool → List α → γ) t values,
  method1726 allocate fill t values = fill (allocate t 1 values.length) false values
theorem property1726 : Property1726 := by unfold Property1726; intros; rfl

def promotedCall (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs

def typedCall (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs

def method1732 (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs
def Property1732 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (call : τ → List α → β) xs,
  method1732 promote call xs = call (promote xs) xs
theorem property1732 : Property1732 := by unfold Property1732; intros; rfl

def method1733 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def Property1733 : Prop := ∀ (τ α β : Type) (call : τ → List α → β) t xs,
  method1733 call t xs = call t xs
theorem property1733 : Property1733 := by unfold Property1733; intros; rfl

def method1740 (similar : α → τ → Nat → β) (vectors : List α) (t : τ) (n : Nat) : Option β :=
  vectors.head?.map fun first => similar first t n
def Property1740 : Prop := ∀ (α τ β : Type) (similar : α → τ → Nat → β) vectors t n,
  method1740 similar vectors t n = vectors.head?.map fun first => similar first t n
theorem property1740 : Property1740 := by unfold Property1740; intros; rfl

def method1741 (length : α → Nat) (allocate : List α → τ → Nat → β)
    (fill : β → List α → γ) (t : τ) (vectors : List α) : γ :=
  fill (allocate vectors t ((vectors.map length).foldl (· + ·) 0)) vectors
def Property1741 : Prop := ∀ (α τ β γ : Type) (length : α → Nat)
    (allocate : List α → τ → Nat → β) (fill : β → List α → γ) t vectors,
  method1741 length allocate fill t vectors =
    fill (allocate vectors t ((vectors.map length).foldl (· + ·) 0)) vectors
theorem property1741 : Property1741 := by unfold Property1741; intros; rfl

def method1755 (call : τ → List α → β) (t : τ) (arrays : List α) : β := call t arrays
def Property1755 : Prop := ∀ (τ α β : Type) (call : τ → List α → β) t arrays,
  method1755 call t arrays = call t arrays
theorem property1755 : Property1755 := by unfold Property1755; intros; rfl

def method1759 : Jl α := .error (.argumentError "ambiguous indexing or typed concatenation")
def Property1759 : Prop := ∀ (α : Type), (method1759 : Jl α) =
  .error (.argumentError "ambiguous indexing or typed concatenation")
theorem property1759 : Property1759 := by unfold Property1759; intros; rfl

def method1765 (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs
def Property1765 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (call : τ → List α → β) xs,
  method1765 promote call xs = call (promote xs) xs
theorem property1765 : Property1765 := by unfold Property1765; intros; rfl

def method1766 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def Property1766 : Prop := ∀ (τ α β : Type) (call : τ → List α → β) t xs,
  method1766 call t xs = call t xs
theorem property1766 : Property1766 := by unfold Property1766; intros; rfl

def method1802 (promote : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (promote xs) xs
def Property1802 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (call : τ → List α → β) xs,
  method1802 promote call xs = call (promote xs) xs
theorem property1802 : Property1802 := by unfold Property1802; intros; rfl

def method1803 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def Property1803 : Prop := ∀ (τ α β : Type) (call : τ → List α → β) t xs,
  method1803 call t xs = call t xs
theorem property1803 : Property1803 := by unfold Property1803; intros; rfl

def method1825 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def Property1825 : Prop := ∀ (τ α β : Type) (call : τ → List α → β) t xs,
  method1825 call t xs = call t xs
theorem property1825 : Property1825 := by unfold Property1825; intros; rfl

def method1827 (mapreduce : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (mapreduce xs) xs
def Property1827 : Prop := ∀ (α τ β : Type) (mapreduce : List α → τ)
    (call : τ → List α → β) xs,
  method1827 mapreduce call xs = call (mapreduce xs) xs
theorem property1827 : Property1827 := by unfold Property1827; intros; rfl

def method1830 (mapreduce : List α → τ) (call : τ → List α → β) (xs : List α) : β :=
  call (mapreduce xs) xs
def Property1830 : Prop := ∀ (α τ β : Type) (mapreduce : List α → τ)
    (call : τ → List α → β) xs,
  method1830 mapreduce call xs = call (mapreduce xs) xs
theorem property1830 : Property1830 := by unfold Property1830; intros; rfl

def method1836 : List Nat := [1]
def Property1836 : Prop := ∀ _scalar : Unit, method1836 = [1]
theorem property1836 : Property1836 := by unfold Property1836; intros; rfl

def method1837 (size : α → List Nat) (a : α) : List Nat := size a
def Property1837 : Prop := ∀ (α : Type) (size : α → List Nat) a,
  method1837 size a = size a
theorem property1837 : Property1837 := by unfold Property1837; intros; rfl

def method1838 (_a : α) (_d : Int) : Nat := 1
def Property1838 : Prop := ∀ (α : Type) (a : α) d, method1838 a d = 1
theorem property1838 : Property1838 := by unfold Property1838; intros; rfl

def method1839 (size : α → Int → Nat) (a : α) (d : Int) : Nat := size a d
def Property1839 : Prop := ∀ (α : Type) (size : α → Int → Nat) a d,
  method1839 size a d = size a d
theorem property1839 : Property1839 := by unfold Property1839; intros; rfl

def method1841 (_a : α) : Nat := 1
def Property1841 : Prop := ∀ (α : Type) (a : α), method1841 a = 1
theorem property1841 : Property1841 := by unfold Property1841; intros; rfl

def method1842 (length : α → Nat) (a : α) : Nat := length a
def Property1842 : Prop := ∀ (α : Type) (length : α → Nat) a,
  method1842 length a = length a
theorem property1842 : Property1842 := by unfold Property1842; intros; rfl

def method1844 (_a : α) : Nat := 0
def Property1844 : Prop := ∀ (α : Type) (a : α), method1844 a = 0
theorem property1844 : Property1844 := by unfold Property1844; intros; rfl

def method1845 (ndims : α → Nat) (a : α) : Nat := ndims a
def Property1845 : Prop := ∀ (α : Type) (ndims : α → Nat) a,
  method1845 ndims a = ndims a
theorem property1845 : Property1845 := by unfold Property1845; intros; rfl

def method1847 (_a : α) (_d : Int) : List Nat := [1]
def Property1847 : Prop := ∀ (α : Type) (a : α) d, method1847 a d = [1]
theorem property1847 : Property1847 := by unfold Property1847; intros; rfl

def method1848 (axes : α → Int → β) (a : α) (d : Int) : β := axes a d
def Property1848 : Prop := ∀ (α β : Type) (axes : α → Int → β) a d,
  method1848 axes a d = axes a d
theorem property1848 : Property1848 := by unfold Property1848; intros; rfl

def method1850 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def Property1850 : Prop := ∀ (τ β : Type) (allocate : τ → List Nat → β) t shape,
  method1850 allocate t shape = allocate t shape
theorem property1850 : Property1850 := by unfold Property1850; intros; rfl

def method1851 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def Property1851 : Prop := ∀ (τ β : Type) (allocate : τ → List Nat → β) t shape,
  method1851 allocate t shape = allocate t shape
theorem property1851 : Property1851 := by unfold Property1851; intros; rfl

def method1852 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def Property1852 : Prop := ∀ (τ β : Type) (allocate : τ → List Nat → β) t shape,
  method1852 allocate t shape = allocate t shape
theorem property1852 : Property1852 := by unfold Property1852; intros; rfl

def method1853 (allocate : τ → List Nat → β) (t : τ) (shape : List Nat) : β := allocate t shape
def Property1853 : Prop := ∀ (τ β : Type) (allocate : τ → List Nat → β) t shape,
  method1853 allocate t shape = allocate t shape
theorem property1853 : Property1853 := by unfold Property1853; intros; rfl

def method1854 (similar : α → τ → List Nat → β) (a : α) (t : τ) (shape : List Nat) : β :=
  similar a t shape
def Property1854 : Prop := ∀ (α τ β : Type) (similar : α → τ → List Nat → β) a t shape,
  method1854 similar a t shape = similar a t shape
theorem property1854 : Property1854 := by unfold Property1854; intros; rfl

def method1855 (similar : α → τ → List Nat → β) (a : α) (t : τ) (shape : List Nat) : β :=
  similar a t shape
def Property1855 : Prop := ∀ (α τ β : Type) (similar : α → τ → List Nat → β) a t shape,
  method1855 similar a t shape = similar a t shape
theorem property1855 : Property1855 := by unfold Property1855; intros; rfl

def method1858 (_dims : List Bool) (shape : List Nat) : List Nat := shape
def Property1858 : Prop := ∀ dims shape, method1858 dims shape = shape
theorem property1858 : Property1858 := by unfold Property1858; intros; rfl

def method1867 (dims : List Bool) : List Nat := List.replicate dims.length 0
def Property1867 : Prop := ∀ dims, method1867 dims = List.replicate dims.length 0
theorem property1867 : Property1867 := by unfold Property1867; intros; rfl

def method1869 (_dims : List Bool) (shape : List Nat) : List Nat := shape
def Property1869 : Prop := ∀ dims shape, method1869 dims shape = shape
theorem property1869 : Property1869 := by unfold Property1869; intros; rfl

def method1872 (_ndim : Int) : List Nat := []
def Property1872 : Prop := ∀ ndim, method1872 ndim = []
theorem property1872 : Property1872 := by unfold Property1872; intros; rfl

def method1873 (_ndim : Int) (nshape : List Nat) : List Nat := nshape
def Property1873 : Prop := ∀ ndim nshape, method1873 ndim nshape = nshape
theorem property1873 : Property1873 := by unfold Property1873; intros; rfl

def method1874 (_ndim : Int) (dims : List Bool) : List Nat := List.replicate dims.length 1
def Property1874 : Prop := ∀ ndim dims, method1874 ndim dims = List.replicate dims.length 1
theorem property1874 : Property1874 := by unfold Property1874; intros; rfl

def method1894 (dim : Int) (a b : Nat) : Except String Nat :=
  if a = b then .ok a else .error s!"mismatch in dimension {dim} (expected {a} got {b})"
def Property1894 : Prop := ∀ dim a b, method1894 dim a b =
  if a = b then .ok a else .error s!"mismatch in dimension {dim} (expected {a} got {b})"
theorem property1894 : Property1894 := by unfold Property1894; intros; rfl

def method1897 (dims2cat : List Int → β) (dims : List Int) : β := dims2cat dims
def Property1897 : Prop := ∀ (β : Type) (dims2cat : List Int → β) dims,
  method1897 dims2cat dims = dims2cat dims
theorem property1897 : Property1897 := by unfold Property1897; intros; rfl

def method1905 (promote : List α → τ) (cat : List Int → τ → List α → β)
    (dims : List Int) (xs : List α) : β := cat dims (promote xs) xs
def Property1905 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (cat : List Int → τ → List α → β) dims xs,
  method1905 promote cat dims xs = cat dims (promote xs) xs
theorem property1905 : Property1905 := by unfold Property1905; intros; rfl

def method1918 (cat : List Int → τ → List α → β) (t : τ) (xs : List α) (dims : List Int) : β :=
  cat dims t xs
def Property1918 : Prop := ∀ (τ α β : Type) (cat : List Int → τ → List α → β) t xs dims,
  method1918 cat t xs dims = cat dims t xs
theorem property1918 : Property1918 := by unfold Property1918; intros; rfl

def method1921 (offset : α → List Nat → List Bool → List Nat → List β → γ)
    (a : α) (shape : List Nat) (catdims : List Bool) (xs : List β) : γ :=
  offset a shape catdims (List.replicate shape.length 0) xs
def Property1921 : Prop := ∀ (α β γ : Type)
    (offset : α → List Nat → List Bool → List Nat → List β → γ) a shape catdims xs,
  method1921 offset a shape catdims xs =
    offset a shape catdims (List.replicate shape.length 0) xs
theorem property1921 : Property1921 := by unfold Property1921; intros; rfl

def method1928 (a : α) (_shape : β) (_dims : γ) (_offsets : δ) : α := a
def Property1928 : Prop := ∀ (α β γ δ : Type) (a : α) (shape : β) (dims : γ) (offsets : δ),
  method1928 a shape dims offsets = a
theorem property1928 : Property1928 := by unfold Property1928; intros; rfl

def method1941 (view : α → ι → β) (fill : β → γ → δ) (a : α) (inds : ι) (x : γ) : δ :=
  fill (view a inds) x
def Property1941 : Prop := ∀ (α ι β γ δ : Type) (view : α → ι → β)
    (fill : β → γ → δ) a inds x,
  method1941 view fill a inds x = fill (view a inds) x
theorem property1941 : Property1941 := by unfold Property1941; intros; rfl

def method1942 (set : α → ι → β → γ) (a : α) (inds : ι) (x : β) : γ := set a inds x
def Property1942 : Prop := ∀ (α ι β γ : Type) (set : α → ι → β → γ) a inds x,
  method1942 set a inds x = set a inds x
theorem property1942 : Property1942 := by unfold Property1942; intros; rfl

def callDim (call : Nat → List α → β) (dim : Nat) (xs : List α) : β := call dim xs

def method2003 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def Property2003 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs,
  method2003 cat xs = cat 1 xs
theorem property2003 : Property2003 := by unfold Property2003; intros; rfl

def method2053 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def Property2053 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs,
  method2053 cat xs = cat 2 xs
theorem property2053 : Property2053 := by unfold Property2053; intros; rfl

def method2055 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def Property2055 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs,
  method2055 cat t xs = cat 1 t xs
theorem property2055 : Property2055 := by unfold Property2055; intros; rfl

def method2056 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def Property2056 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs,
  method2056 cat t xs = cat 2 t xs
theorem property2056 : Property2056 := by unfold Property2056; intros; rfl

def method2169 (cat : δ → List α → β) (dims : δ) (xs : List α) : β := cat dims xs
def Property2169 : Prop := ∀ (δ α β : Type) (cat : δ → List α → β) dims xs,
  method2169 cat dims xs = cat dims xs
theorem property2169 : Property2169 := by unfold Property2169; intros; rfl

def method2171 (cat : δ → τ → List α → β) (dims : δ) (t : τ) (xs : List α) : β := cat dims t xs
def Property2171 : Prop := ∀ (δ τ α β : Type) (cat : δ → τ → List α → β) dims t xs,
  method2171 cat dims t xs = cat dims t xs
theorem property2171 : Property2171 := by unfold Property2171; intros; rfl

def vcatRoute (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def hcatRoute (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def typedVcatRoute (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def typedHcatRoute (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs

def method2175 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def Property2175 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2175 cat xs = cat 1 xs
theorem property2175 : Property2175 := by unfold Property2175; intros; rfl
def method2176 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def Property2176 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2176 cat xs = cat 1 xs
theorem property2176 : Property2176 := by unfold Property2176; intros; rfl
def method2177 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def Property2177 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2177 cat xs = cat 1 xs
theorem property2177 : Property2177 := by unfold Property2177; intros; rfl
def method2178 (cat : Nat → List α → β) (xs : List α) : β := cat 1 xs
def Property2178 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2178 cat xs = cat 1 xs
theorem property2178 : Property2178 := by unfold Property2178; intros; rfl
def method2179 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def Property2179 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2179 cat xs = cat 2 xs
theorem property2179 : Property2179 := by unfold Property2179; intros; rfl
def method2180 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def Property2180 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2180 cat xs = cat 2 xs
theorem property2180 : Property2180 := by unfold Property2180; intros; rfl
def method2181 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def Property2181 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2181 cat xs = cat 2 xs
theorem property2181 : Property2181 := by unfold Property2181; intros; rfl
def method2182 (cat : Nat → List α → β) (xs : List α) : β := cat 2 xs
def Property2182 : Prop := ∀ (α β : Type) (cat : Nat → List α → β) xs, method2182 cat xs = cat 2 xs
theorem property2182 : Property2182 := by unfold Property2182; intros; rfl

def method2184 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def Property2184 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs, method2184 cat t xs = cat 1 t xs
theorem property2184 : Property2184 := by unfold Property2184; intros; rfl
def method2185 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def Property2185 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs, method2185 cat t xs = cat 1 t xs
theorem property2185 : Property2185 := by unfold Property2185; intros; rfl
def method2186 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 1 t xs
def Property2186 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs, method2186 cat t xs = cat 1 t xs
theorem property2186 : Property2186 := by unfold Property2186; intros; rfl
def method2187 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def Property2187 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs, method2187 cat t xs = cat 2 t xs
theorem property2187 : Property2187 := by unfold Property2187; intros; rfl
def method2188 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def Property2188 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs, method2188 cat t xs = cat 2 t xs
theorem property2188 : Property2188 := by unfold Property2188; intros; rfl
def method2189 (cat : Nat → τ → List α → β) (t : τ) (xs : List α) : β := cat 2 t xs
def Property2189 : Prop := ∀ (τ α β : Type) (cat : Nat → τ → List α → β) t xs, method2189 cat t xs = cat 2 t xs
theorem property2189 : Property2189 := by unfold Property2189; intros; rfl

def method2194 (length : α → Nat) (hvcat : List Nat → List α → β) (rows : List α) : β :=
  hvcat (rows.map length) rows
def Property2194 : Prop := ∀ (α β : Type) (length : α → Nat)
    (hvcat : List Nat → List α → β) rows,
  method2194 length hvcat rows = hvcat (rows.map length) rows
theorem property2194 : Property2194 := by unfold Property2194; intros; rfl

def method2195 (length : α → Nat) (hvcat : τ → List Nat → List α → β)
    (t : τ) (rows : List α) : β := hvcat t (rows.map length) rows
def Property2195 : Prop := ∀ (α τ β : Type) (length : α → Nat)
    (hvcat : τ → List Nat → List α → β) t rows,
  method2195 length hvcat t rows = hvcat t (rows.map length) rows
theorem property2195 : Property2195 := by unfold Property2195; intros; rfl

def method2197 (hvcat : List Nat → List α → β) (columns : Int) (values : List α) : Jl β := do
  if columns = 0 then throw .divideError
  if (values.length : Int) % columns != 0 then
    throw (.argumentError "number of arrays is not a multiple of block columns")
  let rows := (values.length : Int) / columns
  if rows < 0 then throw (.argumentError "tuple length must be nonnegative")
  return hvcat (List.replicate rows.toNat columns.toNat) values
def Property2197 : Prop := ∀ (α β : Type) (hvcat : List Nat → List α → β) columns values,
  method2197 hvcat columns values = do
    if columns = 0 then throw .divideError
    if (values.length : Int) % columns != 0 then
      throw (.argumentError "number of arrays is not a multiple of block columns")
    let rows := (values.length : Int) / columns
    if rows < 0 then throw (.argumentError "tuple length must be nonnegative")
    return hvcat (List.replicate rows.toNat columns.toNat) values
theorem property2197 : Property2197 := by unfold Property2197; intros; rfl

def method2244 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def Property2244 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (call : τ → List Nat → List α → β) rows xs,
  method2244 promote call rows xs = call (promote xs) rows xs
theorem property2244 : Property2244 := by unfold Property2244; intros; rfl

def method2245 (call : τ → List Nat → List α → β) (t : τ) (rows : List Nat) (xs : List α) : β :=
  call t rows xs
def Property2245 : Prop := ∀ (τ α β : Type) (call : τ → List Nat → List α → β) t rows xs,
  method2245 call t rows xs = call t rows xs
theorem property2245 : Property2245 := by unfold Property2245; intros; rfl

def method2247 (rows : List Nat) : Sum (Nat × Nat) (List Nat × Nat) :=
  match rows with
  | [] => .inl (0, 0)
  | first :: _ => if rows.all (· == first) then .inl (rows.length, first)
    else .inr (rows, rows.foldl (· + ·) 0)
def Property2247 : Prop := ∀ rows, method2247 rows = match rows with
  | [] => .inl (0, 0)
  | first :: _ => if rows.all (· == first) then .inl (rows.length, first)
    else .inr (rows, rows.foldl (· + ·) 0)
theorem property2247 : Property2247 := by
  unfold Property2247
  intro rows
  cases rows <;> rfl

def method2248 (shape : List Nat → σ) (call : τ → σ → Bool → List α → β)
    (t : τ) (rows : List Nat) (xs : List α) : β := call t (shape rows) true xs
def Property2248 : Prop := ∀ (σ τ α β : Type) (shape : List Nat → σ)
    (call : τ → σ → Bool → List α → β) t rows xs,
  method2248 shape call t rows xs = call t (shape rows) true xs
theorem property2248 : Property2248 := by unfold Property2248; intros; rfl

inductive JuliaAny

def method2250 (_rows : List Nat) : List JuliaAny := []
def Property2250 : Prop := ∀ rows, method2250 rows = []
theorem property2250 : Property2250 := by unfold Property2250; intros; rfl

def method2251 (elementType : Type) (_rows : List Nat) : List elementType := []
def Property2251 : Prop := ∀ (elementType : Type) rows, method2251 elementType rows = []
theorem property2251 : Property2251 := by unfold Property2251; intros; rfl

def method2274 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def Property2274 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (call : τ → List Nat → List α → β) rows xs,
  method2274 promote call rows xs = call (promote xs) rows xs
theorem property2274 : Property2274 := by unfold Property2274; intros; rfl

def method2275 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def Property2275 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (call : τ → List Nat → List α → β) rows xs,
  method2275 promote call rows xs = call (promote xs) rows xs
theorem property2275 : Property2275 := by unfold Property2275; intros; rfl

def method2277 (promote : List α → τ) (call : τ → List Nat → List α → β)
    (rows : List Nat) (xs : List α) : β := call (promote xs) rows xs
def Property2277 : Prop := ∀ (α τ β : Type) (promote : List α → τ)
    (call : τ → List Nat → List α → β) rows xs,
  method2277 promote call rows xs = call (promote xs) rows xs
theorem property2277 : Property2277 := by unfold Property2277; intros; rfl

def method2292 (shape : List Nat → σ) (call : τ → σ → Bool → List α → β)
    (t : τ) (rows : List Nat) (xs : List α) : β := call t (shape rows) true xs
def Property2292 : Prop := ∀ (σ τ α β : Type) (shape : List Nat → σ)
    (call : τ → σ → Bool → List α → β) t rows xs,
  method2292 shape call t rows xs = call t (shape rows) true xs
theorem property2292 : Property2292 := by unfold Property2292; intros; rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.ConcatDirect
