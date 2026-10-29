import JuliaLean.MultidimCov.ArrayV2Core

/-!
Storage queries on types and the `@_safeindex` rewrite (master `base/array.jl:132-264`),
with `jl_stored_inline`/`jl_islayout_inline`/`union_isinlinable`/`jl_datatype_isinlinealloc`
(`src/datatype.c:385-445`) and `aligned_sizeof` (`base/runtime_internals.jl:667-689`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-! ### Types and their layout -/

/-- A concrete `DataType` with a layout: `isbitstype`, `name->mayinlinealloc`
(immutable), whether its layout has pointer fields, whether one of them may be
`#undef` or the field descriptors are too wide (`n_uninitialized != 0` or
`fielddesc_type > 1`), and `sizeof`/`datatype_alignment`. -/
structure DT where
  name : Nat
  isbits : Bool
  mayInline : Bool
  ptrs : Bool
  undefPtrs : Bool
  size : Nat
  align : Nat

/-- A well-formed layout: an `isbitstype` is exactly an inline-allocatable type
without pointer fields; the alignment is a power of two dividing the size. -/
def DT.WF (d : DT) : Prop :=
  d.isbits = (d.mayInline && !d.ptrs) ∧ (∃ k, d.align = 2 ^ k) ∧ d.align ∣ d.size

/-- The types the storage queries distinguish. -/
inductive JType where
  | any
  | bottom
  /-- An abstract `DataType` such as `Real`. -/
  | abstractDT (name : Nat)
  | dt (d : DT)
  /-- A `Union` of at least two distinct concrete members. -/
  | union (ms : List DT)

/-- `jl_datatype_isinlinealloc(ty, pointerfree)`. -/
def isInlineAlloc (d : DT) (pointerfree : Bool) : Bool :=
  d.mayInline && (!d.ptrs || (!pointerfree && !d.undefPtrs))

/-- `union_isinlinable(ty, pointerfree, …)`: the members of a `Union` are tested with
`pointerfree = 1`; `0` when one is not inlinable, else the member count. -/
def unionIsInlinable : JType → Bool → Nat
  | .dt d, pf => if isInlineAlloc d pf then 1 else 0
  | .union ms, _ => if ms.all (fun d => isInlineAlloc d true) then ms.length else 0
  | _, _ => 0

/-- `jl_islayout_inline(eltype, …)`: `countbits = union_isinlinable(eltype, 0, …)`,
`countbits > 0 && countbits < 127`. -/
def isLayoutInline (T : JType) : Bool :=
  let c := unionIsInlinable T false
  0 < c && c < 127

/-- base/array.jl:190 `allocatedinline(T) = ccall(:jl_stored_inline, …) != 0`
(`jl_stored_inline` is `jl_islayout_inline`). -/
def m190 (T : JType) : Bool := isLayoutInline T

/-- base/array.jl:206 `isbitsunion(u::Type) = u isa Union && allocatedinline(u)`. -/
def m206 (u : JType) : Bool :=
  match u with
  | .union _ => m190 u
  | _ => false

/-- `isbitstype(T)`. -/
def JType.isbits : JType → Bool
  | .dt d => d.isbits
  | _ => false

/-- The documented meaning: `isbitsunion(u)` holds exactly for a `Union` whose
members are all `isbitstype` (docstring base/array.jl:192-195), and
`allocatedinline` agrees with it on unions (comment base/runtime_internals.jl:672;
devdocs "isbits Union optimizations"); every `isbitstype` is stored inline and
`Any`, abstract types, `Union{}` and mutable types are not. -/
def P206 : Prop :=
  (∀ ms : List DT, 2 ≤ ms.length → (ms.map DT.name).Nodup → (∀ d ∈ ms, d.WF) →
    (m206 (.union ms) = true ↔ ∀ d ∈ ms, d.isbits = true) ∧ m190 (.union ms) = m206 (.union ms)) ∧
  (∀ T : JType, (∀ ms, T ≠ .union ms) → m206 T = false) ∧
  (∀ d : DT, d.WF → d.isbits = true → m190 (.dt d) = true) ∧
  (∀ d : DT, d.mayInline = false → m190 (.dt d) = false) ∧
  m190 .any = false ∧ m190 .bottom = false ∧ ∀ n, m190 (.abstractDT n) = false

/-- `Val{i}` for `i = 1:127`: distinct singleton `isbitstype`s (size 0, alignment 1). -/
def valTypes : List DT := (List.range 127).map fun i => ⟨i, true, true, false, false, 0, 1⟩

theorem p206_refuted : ¬ P206 := by
  intro h
  have hn : (valTypes.map DT.name).Nodup := by
    simp [valTypes, List.map_map, Function.comp_def, List.nodup_range]
  have hwf : ∀ d ∈ valTypes, d.WF := by
    intro d hd
    simp only [valTypes, List.mem_map] at hd
    obtain ⟨i, _, rfl⟩ := hd
    exact ⟨rfl, ⟨0, rfl⟩, Nat.dvd_zero 1⟩
  have hb : ∀ d ∈ valTypes, d.isbits = true := by
    intro d hd
    simp only [valTypes, List.mem_map] at hd
    obtain ⟨i, _, rfl⟩ := hd; rfl
  have := ((h.1 valTypes (by simp [valTypes]) hn hwf).1).2 hb
  have hall : valTypes.all (fun d => isInlineAlloc d true) = true := by simp [valTypes, isInlineAlloc]
  have hl : valTypes.length = 127 := by simp [valTypes]
  simp [m206, m190, isLayoutInline, unionIsInlinable, hall, hl] at this

/-! ### `aligned_sizeof`, `elsize`, `sizeof` -/

/-- `LLT_ALIGN(x, sz) = (x + sz - 1) & -sz`, for a power-of-two `sz`: `x` rounded up to a
multiple of `sz`. -/
def lltAlign (x sz : Nat) : Nat := (x + sz - 1) / sz * sz

/-- `uniontype_layout(T)`: the inline size and alignment of a `Union` (the largest
member size and alignment, `union_isinlinable` with `nbytes`/`align`). -/
def unionLayout (ms : List DT) : Nat × Nat :=
  (ms.foldr (fun d s => max d.size s) 0, ms.foldr (fun d a => max d.align a) 0)

/-- `Core.sizeof(Ptr{Cvoid})`. -/
def ptrSize : Nat := 8

/-- base/runtime_internals.jl:667 `aligned_sizeof(T)`. -/
def alignedSizeof (T : JType) : Nat :=
  match T with
  | .union ms => if m190 T then lltAlign (unionLayout ms).1 (unionLayout ms).2 else ptrSize
  | .dt d => if m190 T then lltAlign d.size d.align else ptrSize
  | _ => ptrSize

/-- base/array.jl:218 `elsize(::Type{A}) where {T,A<:Array{T}} = aligned_sizeof(T)`. -/
def m218 (T : JType) : Nat := alignedSizeof T

/-- base/array.jl:219 `elsize(::Type{Ptr{T}})`: `sizeof(Ptr{Any})` for `Any`; for a
non-`DataType` `sizeof(Any)` throws `ErrorException` (as does `Core.sizeof` of an
abstract type); else `LLT_ALIGN(Core.sizeof(T), datatype_alignment(T))`. -/
def m219 (T : JType) : R Nat :=
  match T with
  | .any => .ok ptrSize
  | .dt d => .ok (lltAlign d.size d.align)
  | _ => .error .argument

/-- base/array.jl:226 `elsize(::Type{Union{}}) = 0`. -/
def m226 : Nat := 0

/-- base/array.jl:227 `elsize(::Type{Union{}}, slurp...) = throw(MethodError(elsize, …))`. -/
def m227 (_slurp : List α) : R Nat := .error .method

/-- base/array.jl:229 `sizeof(a::Array) = length(a) * elsize(typeof(a))`. -/
def m229 (T : JType) (a : Arr β) : Int := length a * m218 T

theorem lltAlign_of_dvd (x a : Nat) (ha : 0 < a) (h : a ∣ x) : lltAlign x a = x := by
  obtain ⟨k, rfl⟩ := h
  unfold lltAlign
  have : (a * k + a - 1) / a = k := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; omega
    · rw [Nat.succ_mul, Nat.mul_comm]; omega
  rw [this, Nat.mul_comm]

/-- Element strides (`elsize`, docstring of `sizeof`, base/essentials.jl): an array of
an `isbitstype` `T` uses `sizeof(T)` bytes per element, and `sizeof(a)` is
`length(a) * sizeof(T)` (the doctest `sizeof([1.0:10.0;]) == 80`); an array of a
non-inline type holds pointers (`elsize == sizeof(Ptr)`); the pointer stride of
`Ptr{T}` agrees with the array stride for every `isbitstype` and is `sizeof(Ptr)` for
`Any`; `elsize(Union{}) == 0`, and extra arguments are a `MethodError`. -/
def P218 : Prop :=
  (∀ {β : Type} (d : DT) (a : Arr β), d.WF → d.isbits = true →
    m218 (.dt d) = d.size ∧ m229 (.dt d) a = length a * d.size ∧ m219 (.dt d) = .ok (m218 (.dt d))) ∧
  (∀ T : JType, m190 T = false → m218 T = ptrSize) ∧
  m219 .any = .ok ptrSize ∧ m226 = 0 ∧ ∀ (xs : List Nat), m227 xs = .error .method

theorem p218 : P218 := by
  refine ⟨fun {β} d a hwf hb => ?_, fun T hT => ?_, rfl, rfl, fun _ => rfl⟩
  · obtain ⟨h1, ⟨k, hk⟩, hdv⟩ := hwf
    have hin : m190 (.dt d) = true := by
      rw [hb] at h1
      have hm : d.mayInline = true ∧ d.ptrs = false := by
        have := h1.symm; simpa [Bool.and_eq_true] using this
      simp [m190, isLayoutInline, unionIsInlinable, isInlineAlloc, hm.1, hm.2]
    have hpos : 0 < d.align := by rw [hk]; exact Nat.two_pow_pos k
    have hs : m218 (.dt d) = d.size := by
      simp only [m218, alignedSizeof, hin, if_true]; exact lltAlign_of_dvd _ _ hpos hdv
    refine ⟨hs, by simp only [m229, hs], ?_⟩
    rw [hs]; simp only [m219]; rw [lltAlign_of_dvd _ _ hpos hdv]
  · cases T <;> simp_all [m218, alignedSizeof]

/-! ### `unsafe_copyto!` on pointers -/

/-- Process memory as bytes. -/
abbrev Bytes := Nat → UInt8

/-- `memmove(dest, src, n)`: byte `b` of the destination window takes the old byte
at `src + (b - dest)`; overlapping windows read the old contents. -/
def memmove (m : Bytes) (dest src n : Nat) : Bytes :=
  fun b => if dest ≤ b ∧ b < dest + n then m (src + (b - dest)) else m b

/-- base/array.jl:259 `unsafe_copyto!(dest::Ptr{T}, src::Ptr{T}, n)`:
`memmove(dest, src, n * aligned_sizeof(T))`, returning `dest`. -/
def m259 (T : JType) (m : Bytes) (dest src : Nat) (n : Nat) : Bytes × Nat :=
  (memmove m dest src (n * alignedSizeof T), dest)

/-- The `s` bytes of element `k` of a pointer `p` with stride `s`. -/
def elemBytes (m : Bytes) (p s k : Nat) : List UInt8 := (List.range s).map fun j => m (p + k * s + j)

/-- `unsafe_copyto!(dest, src, n)` copies `n` elements (docstring base/array.jl:249-258):
element `k < n` at `dest` is the old element `k` at `src`, even when the windows
overlap; bytes outside the destination window are unchanged; it returns `dest`. -/
def P259 : Prop := ∀ (T : JType) (m : Bytes) (dest src n : Nat),
    (m259 T m dest src n).2 = dest ∧
    (∀ k < n, elemBytes (m259 T m dest src n).1 dest (alignedSizeof T) k = elemBytes m src (alignedSizeof T) k) ∧
    (∀ b, (b < dest ∨ dest + n * alignedSizeof T ≤ b) → (m259 T m dest src n).1 b = m b)

theorem p259 : P259 := by
  intro T m dest src n
  refine ⟨rfl, fun k hk => ?_, fun b hb => ?_⟩
  · unfold elemBytes
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [m259, memmove]
    have h1 : k * alignedSizeof T + j < n * alignedSizeof T := by
      have : (k + 1) * alignedSizeof T ≤ n * alignedSizeof T := Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at this; omega
    rw [if_pos ⟨by omega, by omega⟩]; congr 1; omega
  · simp only [m259, memmove]; rw [if_neg (by omega)]

/-! ### `@_safeindex` -/

/-- Expression heads `_safeindex` distinguishes. -/
inductive Head where
  | assign
  | ref
  | call
  | escape
  | other (n : Nat)
  deriving DecidableEq

/-- Julia expressions: an atom (symbol, literal, `GlobalRef`), the two `__safe_`
`GlobalRef`s, or `Expr(head, args...)`. -/
inductive JExpr where
  | atom (n : Nat)
  | safeGet
  | safeSet
  | expr (h : Head) (args : List JExpr)

mutual
/-- base/array.jl:135 `_safeindex(ex)`. -/
def m135 : JExpr → JExpr
  | .expr .assign (.expr .ref (xs :: idx) :: rhs :: rest) =>
    let _ := rest
    .expr .call (.safeSet :: xs :: m135 rhs :: m135List idx)
  | .expr .ref args => .expr .call (.safeGet :: args)
  | .expr h args => .expr h (m135List args)
  | e => e
/-- `for i = 1:length(args); args[i] = _safeindex(ex.args[i]); end`. -/
def m135List : List JExpr → List JExpr
  | [] => []
  | e :: es => m135 e :: m135List es
end

/-- base/array.jl:132 `macro _safeindex(ex) = esc(_safeindex(ex))`. -/
def m132 (ex : JExpr) : JExpr := .expr .escape [m135 ex]

mutual
/-- Does an expression mention a `__safe_` function? -/
def hasSafe : JExpr → Bool
  | .safeGet => true
  | .safeSet => true
  | .atom _ => false
  | .expr _ args => hasSafeList args
def hasSafeList : List JExpr → Bool
  | [] => false
  | e :: es => hasSafe e || hasSafeList es
end

mutual
/-- Undo the rewrite: `__safe_getindex(xs, i...)` back to `xs[i...]` and
`__safe_setindex!(xs, x, i...)` back to `xs[i...] = x`. -/
def restore : JExpr → JExpr
  | .expr .call (.safeGet :: args) => .expr .ref args
  | .expr .call (.safeSet :: xs :: rhs :: idx) => .expr .assign [.expr .ref (xs :: restoreList idx), restore rhs]
  | .expr h args => .expr h (restoreList args)
  | e => e
def restoreList : List JExpr → List JExpr
  | [] => []
  | e :: es => restore e :: restoreList es
end

/-- A well-formed expression, as the parser produces: assignments have a left- and a
right-hand side and an indexing has a collection (Julia's `ex.args[2]` and
`lhs.args[1]` would throw `BoundsError` otherwise). -/
def WFE : JExpr → Bool
  | .expr .assign [l, r] => WFE l && WFE r
  | .expr .assign _ => false
  | .expr .ref [] => false
  | .expr _ args => args.attach.all fun ⟨e, _⟩ => WFE e
  | _ => true

/-- Nesting depth. -/
def depth : JExpr → Nat
  | .expr _ args => (args.attach.map fun ⟨e, _⟩ => depth e).foldr max 0 + 1
  | _ => 0

theorem depth_lt {h : Head} {args : List JExpr} {e : JExpr} (he : e ∈ args) : depth e < depth (.expr h args) := by
  rw [depth]
  have : depth e ≤ (args.attach.map fun ⟨e, _⟩ => depth e).foldr max 0 := by
    have hm : depth e ∈ args.attach.map (fun ⟨e, _⟩ => depth e) :=
      List.mem_map.mpr ⟨⟨e, he⟩, List.mem_attach _ _, rfl⟩
    generalize args.attach.map (fun ⟨e, _⟩ => depth e) = l at hm
    induction l with
    | nil => simp at hm
    | cons x xs ih =>
      simp only [List.foldr_cons, List.mem_cons] at hm ⊢
      rcases hm with hm | hm
      · subst hm; omega
      · have := ih hm; omega
  omega

theorem wfe_args {h : Head} {args : List JExpr} (hw : WFE (.expr h args) = true) (hh : h ≠ .assign) :
    ∀ e ∈ args, WFE e = true := by
  intro e he
  cases h <;> (try exact absurd rfl hh) <;>
    (cases args with
     | nil => simp at he
     | cons a as =>
       simp only [WFE, List.all_eq_true] at hw
       exact hw ⟨e, he⟩ (List.mem_attach _ _))

theorem hasSafe_args {h : Head} {args : List JExpr} (hs : hasSafe (.expr h args) = false) :
    ∀ e ∈ args, hasSafe e = false := by
  simp only [hasSafe] at hs
  induction args with
  | nil => simp
  | cons a as ih =>
    simp only [hasSafeList, Bool.or_eq_false_iff] at hs
    intro e he; simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hs.1
    · exact ih hs.2 e he

theorem m135_shape (h : Head) (args : List JExpr) : ∃ h' a', m135 (.expr h args) = .expr h' a' := by
  unfold m135; split <;> first | exact ⟨_, _, rfl⟩ | (rename_i hne; exact absurd rfl (hne _ _))

theorem m135_ne_safe (e : JExpr) (h1 : e ≠ .safeGet) (h2 : e ≠ .safeSet) :
    m135 e ≠ .safeGet ∧ m135 e ≠ .safeSet := by
  cases e with
  | expr h args => obtain ⟨h', a', hm⟩ := m135_shape h args; rw [hm]; simp
  | atom n => simp [m135]
  | safeGet => exact absurd rfl h1
  | safeSet => exact absurd rfl h2

theorem m135List_eq (es : List JExpr) : m135List es = es.map m135 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [m135List, ih]

theorem restoreList_eq (es : List JExpr) : restoreList es = es.map restore := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [restoreList, ih]

/-- `restore` on an expression whose head is not `call`, or whose first argument is
not a `__safe_` function, maps over the arguments. -/
theorem restore_generic (h : Head) (args : List JExpr)
    (hne : ∀ rest, h = .call → args ≠ .safeGet :: rest ∧ args ≠ .safeSet :: rest) :
    restore (.expr h args) = .expr h (args.map restore) := by
  rw [← restoreList_eq]
  cases h with
  | call =>
    cases args with
    | nil => rfl
    | cons a rest =>
      have := hne rest rfl
      cases a with
      | safeGet => exact absurd rfl this.1
      | safeSet => exact absurd rfl this.2
      | atom _ => rfl
      | expr _ _ => rfl
  | _ => rfl

theorem restore_m135_aux : ∀ (n : Nat) (e : JExpr), depth e ≤ n → WFE e = true → hasSafe e = false →
    restore (m135 e) = e
  | n, .atom _, _, _, _ => rfl
  | _, .safeGet, _, _, hs => by simp [hasSafe] at hs
  | _, .safeSet, _, _, hs => by simp [hasSafe] at hs
  | 0, .expr h args, hd, _, _ => by simp [depth] at hd
  | n + 1, .expr h args, hd, hw, hs => by
    have ih : ∀ e ∈ args, WFE e = true → restore (m135 e) = e := fun e he hwe =>
      restore_m135_aux n e (by have := depth_lt (h := h) he; omega) hwe (hasSafe_args hs e he)
    have hsa := hasSafe_args hs
    have ne_safe : ∀ e ∈ args, e ≠ .safeGet ∧ e ≠ .safeSet := fun e he => by
      have := hsa e he; constructor <;> rintro rfl <;> simp [hasSafe] at this
    have map_id : ∀ (l : List JExpr), (∀ e ∈ l, e ∈ args) → (∀ e ∈ l, WFE e = true) →
        (l.map m135).map restore = l := by
      intro l hl hwl
      rw [List.map_map]
      conv => rhs; rw [← List.map_id l]
      exact List.map_congr_left fun e he => ih e (hl e he) (hwl e he)
    cases h with
    | assign =>
      match args, hw, ih, hsa, ne_safe, map_id with
      | [l, r], hw, ih, hsa, ne_safe, map_id =>
        simp only [WFE, Bool.and_eq_true] at hw
        have refCase : ∀ xs idx, l = .expr .ref (xs :: idx) → restore (m135 (.expr .assign [l, r])) = .expr .assign [l, r] := by
          intro xs idx hl; subst hl
          have hsl := hasSafe_args (hsa (.expr .ref (xs :: idx)) (by simp))
          have hwl := wfe_args hw.1 (by simp)
          show restore (.expr .call (.safeSet :: xs :: m135 r :: m135List idx)) = _
          have hidx : (idx.map m135).map restore = idx := by
            rw [List.map_map]; conv => rhs; rw [← List.map_id idx]
            exact List.map_congr_left fun e he =>
              restore_m135_aux n e (by
                have h1 := depth_lt (h := .ref) (List.mem_cons_of_mem xs he)
                have h2 := depth_lt (h := .assign) (show JExpr.expr .ref (xs :: idx) ∈ [JExpr.expr .ref (xs :: idx), r] by simp)
                omega) (hwl e (List.mem_cons_of_mem xs he)) (hsl e (List.mem_cons_of_mem xs he))
          simp only [restore, restoreList_eq, m135List_eq, hidx, ih r (by simp) hw.2]
        have generic : m135 (.expr .assign [l, r]) = .expr .assign [m135 l, m135 r] →
            restore (m135 (.expr .assign [l, r])) = .expr .assign [l, r] := by
          intro hm
          rw [hm, restore_generic _ _ (by simp)]
          have := map_id [l, r] (by simp) (by simp [hw.1, hw.2])
          simpa using this
        cases l with
        | atom k => exact generic rfl
        | safeGet => exact absurd rfl (ne_safe _ (by simp)).1
        | safeSet => exact absurd rfl (ne_safe _ (by simp)).2
        | expr h' a =>
          cases h' with
          | ref =>
            cases a with
            | nil => simp [WFE] at hw
            | cons xs idx => exact refCase xs idx rfl
          | assign => exact generic rfl
          | call => exact generic rfl
          | escape => exact generic rfl
          | other k => exact generic rfl
      | [], hw, _, _, _, _ => simp [WFE] at hw
      | [_], hw, _, _, _, _ => simp [WFE] at hw
      | _ :: _ :: _ :: _, hw, _, _, _, _ => simp [WFE] at hw
    | ref => rfl
    | call =>
      have hw' := wfe_args hw (by simp)
      show restore (.expr .call (m135List args)) = _
      rw [m135List_eq, restore_generic]
      · rw [map_id args (fun e he => he) hw']
      · intro rest _
        cases args with
        | nil => simp
        | cons a as =>
          have := m135_ne_safe a (ne_safe a (by simp)).1 (ne_safe a (by simp)).2
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨fun h => this.1 (List.cons.inj h).1, fun h => this.2 (List.cons.inj h).1⟩
    | escape =>
      have hw' := wfe_args hw (by simp)
      show restore (.expr .escape (m135List args)) = _
      rw [m135List_eq, restore_generic _ _ (by simp), map_id args (fun e he => he) hw']
    | other k =>
      have hw' := wfe_args hw (by simp)
      show restore (.expr (.other k) (m135List args)) = _
      rw [m135List_eq, restore_generic _ _ (by simp), map_id args (fun e he => he) hw']

theorem restore_m135 (e : JExpr) (hw : WFE e = true) (hs : hasSafe e = false) : restore (m135 e) = e :=
  restore_m135_aux _ e (Nat.le_refl _) hw hs

/-- `@_safeindex` (docstring base/array.jl:123-131) turns each top-level indexing
`xs[i...]` into `__safe_getindex(xs, i...)` and each indexed assignment
`xs[i...] = x` into `__safe_setindex!(xs, x, i...)`, and changes nothing else: undoing
those two rewrites gives back the original (well-formed, `__safe_`-free) expression;
the macro escapes the result. -/
def P135 : Prop :=
  (∀ e : JExpr, WFE e = true → hasSafe e = false → restore (m135 e) = e) ∧
  (∀ args : List JExpr, m135 (.expr .ref args) = .expr .call (.safeGet :: args)) ∧
  (∀ xs rhs idx, m135 (.expr .assign [.expr .ref (xs :: idx), rhs]) =
    .expr .call (.safeSet :: xs :: m135 rhs :: m135List idx)) ∧
  (∀ e, m132 e = .expr .escape [m135 e])

theorem p135 : P135 := ⟨restore_m135, fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

end JuliaLean.MultidimCov.ArrayV2
