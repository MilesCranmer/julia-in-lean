import JuliaLean.MiscCov.Basic

/-!
# `base/refvalue.jl`, `base/scope.jl`, `base/baseext.jl` (master `bbfa0ce4150`)

Julia values are elements of an abstract type `V`. A Julia type `T` is described
by what the modelled methods use: how a field of type `T` is stored
(`allocatedinline(T)`; otherwise concrete mutable or other), the value an
uninitialized inline field holds, and `convert(T, ·)`, which `new` and
`setfield!` apply implicitly. Objects have addresses (`pointer_from_objref`).
-/

namespace JuliaLean.MiscCov

/-! ## `base/refvalue.jl` -/

namespace RefValue

/-- How a field of type `T` is stored: inline (`allocatedinline(T)`), as a
pointer to a concrete mutable object, or as a pointer to some other boxed value. -/
inductive Layout where
  | inline | mutableConcrete | boxed
  deriving DecidableEq, Repr

/-- The parts of a Julia type `T` the methods depend on. -/
structure Ty (V : Type) where
  layout : Layout
  /-- The bits an uninitialized inline field holds (`new()` leaves them as they are). -/
  zero : V
  /-- `convert(T, x)`. -/
  conv : V → M V

/-- A `RefValue{T}` object: its address and its field `x` (`none` is `#undef`, which
only a pointer field can be). -/
structure Obj (V : Type) where
  addr : Nat
  x : Option V

variable {V : Type}

/-- `RefValue{T}() = new()`, `base/refvalue.jl:7`, allocated at address `a`. -/
def newEmpty (T : Ty V) (a : Nat) : Obj V :=
  { addr := a, x := if T.layout = .inline then some T.zero else none }

/-- `RefValue{T}(x) = new(x)`, `base/refvalue.jl:8`: `new` converts to the field type. -/
def newWith (T : Ty V) (a : Nat) (v : V) : M (Obj V) := do
  let v ← T.conv v
  pure { addr := a, x := some v }

/-- `RefValue(x::T) = RefValue{T}(x)`, `base/refvalue.jl:10`; `typeT` is `typeof(x)`,
whose `convert` returns `x` itself. -/
def newInfer (typeT : Ty V) (a : Nat) (v : V) : M (Obj V) := newWith typeT a v

/-- `isassigned(x::RefValue) = isdefined(x, :x)`, `base/refvalue.jl:36`. -/
def isassigned (r : Obj V) : Bool := r.x.isSome

/-- `getindex(b::RefValue) = b.x`, `base/refvalue.jl:59`. -/
def getindex (r : Obj V) : M V :=
  match r.x with
  | some v => .ok v
  | none => .error .undefRefError

/-- `setindex!(b::RefValue, x) = (b.x = x; b)`, `base/refvalue.jl:60`. -/
def setindex (T : Ty V) (r : Obj V) (v : V) : M (Obj V) := do
  let v ← T.conv v
  pure { r with x := some v }

/-- Where pointers point: `pointer_from_objref` of a mutable object, and the pointer
stored in a boxed (non-inline) field. -/
structure Ptrs (V : Type) where
  objref : V → Nat
  boxed : V → Nat

/-- `unsafe_convert(P::Union{Type{Ptr{T}},Type{Ptr{Cvoid}}}, b::RefValue{T})`,
`base/refvalue.jl:38-54`: the address of the `RefValue` for an inline field; the
object itself for a concrete mutable `T` (reading `b.x`, which throws
`UndefRefError` when unassigned); otherwise the pointer loaded from the field,
with `UndefRefError` for `C_NULL`, which is what an `#undef` field holds. -/
def unsafeConvert (T : Ty V) (P : Ptrs V) (r : Obj V) : M Nat :=
  match T.layout with
  | .inline => .ok r.addr
  | .mutableConcrete =>
    match r.x with
    | some v => .ok (P.objref v)
    | none => .error .undefRefError
  | .boxed =>
    match r.x with
    | none => .error .undefRefError
    | some v => .ok (P.boxed v)

/-- `unsafe_convert(::Type{Ptr{Any}}, b::RefValue{Any}) = pointer_from_objref(b)`,
`base/refvalue.jl:55-57`. -/
def unsafeConvertAny (r : Obj V) : Nat := r.addr

/-- The `isassigned` docstring (`base/refvalue.jl:12-35`) and the obvious contract of
the other methods: a `Ref` of an inline (bits) type is always assigned, a fresh
`Ref` of another type is not; assigning makes it assigned and `ref[]` returns the
converted value; `setindex!` returns the same object; `RefValue(x)` stores `x`;
`unsafe_convert` throws `UndefRefError` exactly for an unassigned non-inline
field and otherwise returns the address of the box, of the object, or the stored
pointer; `unsafe_convert(Ptr{Any}, ::RefValue{Any})` is the box address. -/
def Contract : Prop :=
  ∀ (T : Ty V) (P : Ptrs V) (a : Nat) (v : V),
    (isassigned (newEmpty T a) = true ↔ T.layout = .inline) ∧
    ((T.layout = .inline) → getindex (newEmpty T a) = .ok T.zero) ∧
    ((T.layout ≠ .inline) → getindex (newEmpty T a) = .error .undefRefError) ∧
    (∀ r : Obj V, setindex T r v = (T.conv v).map (fun w => { r with x := some w })) ∧
    (∀ r : Obj V, ∀ w, T.conv v = .ok w →
      ∃ r', setindex T r v = .ok r' ∧ r'.addr = r.addr ∧ isassigned r' = true ∧ getindex r' = .ok w) ∧
    (newWith T a v = (T.conv v).map (fun w => { addr := a, x := some w })) ∧
    (T.conv v = .ok v → newInfer T a v = .ok { addr := a, x := some v }) ∧
    (∀ r : Obj V, (unsafeConvert T P r = .error .undefRefError ↔ T.layout ≠ .inline ∧ r.x = none)) ∧
    (∀ r : Obj V, T.layout = .inline → unsafeConvert T P r = .ok r.addr) ∧
    (∀ r : Obj V, ∀ w, r.x = some w → T.layout = .mutableConcrete → unsafeConvert T P r = .ok (P.objref w)) ∧
    (∀ r : Obj V, ∀ w, r.x = some w → T.layout = .boxed → unsafeConvert T P r = .ok (P.boxed w)) ∧
    (∀ r : Obj V, unsafeConvertAny r = r.addr)

theorem contract_proven : @Contract V := by
  intro T P a v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [isassigned, newEmpty]; split <;> simp_all
  · intro h; simp [getindex, newEmpty, h]
  · intro h; simp [getindex, newEmpty, h]
  · intro r; simp only [setindex]; cases T.conv v <;> rfl
  · intro r w h; exact ⟨{ r with x := some w }, by simp [setindex, h]; rfl, rfl, rfl, rfl⟩
  · simp only [newWith]; cases T.conv v <;> rfl
  · intro h; simp [newInfer, newWith, h]; rfl
  · intro r
    cases hl : T.layout <;> cases hx : r.x <;> simp [unsafeConvert, hl, hx, getindex]
  · intro r h; simp [unsafeConvert, h]
  · intro r w hx h; simp [unsafeConvert, h, hx]
  · intro r w hx h; simp [unsafeConvert, h, hx]
  · intro r; rfl

end RefValue

/-! ## `base/scope.jl` -/

namespace Scope

/-- A scoped value: an identity and `convert(T, ·)` for its type `T`. -/
structure Key (V : Type) where
  id : Nat
  conv : V → M V

variable {V : Type}

/-- `ScopeStorage = PersistentDict{AbstractScopedValue, Any}`: a persistent map, as an
association list in which the first binding of a key wins; `PersistentDict(d, k => v)`
is the map `d` with `k` bound to `v`. -/
abbrev Storage (V : Type) := List (Nat × V)

def Storage.get : Storage V → Nat → Option V
  | [], _ => none
  | (k', v) :: d, k => if k' = k then some v else Storage.get d k

/-- `struct Scope values::ScopeStorage end`. -/
structure Scope (V : Type) where
  values : Storage V

/-- `Scope(scope::Scope) = scope`, `base/scope.jl:28`. -/
def ofScope (s : Scope V) : Scope V := s

/-- `Scope(parent::Union{Nothing, Scope}, key::AbstractScopedValue{T}, value)`,
`base/scope.jl:30-36`. -/
def mk (parent : Option (Scope V)) (key : Key V) (value : V) : M (Scope V) := do
  let val ← key.conv value
  match parent with
  | none => pure ⟨[(key.id, val)]⟩
  | some p => pure ⟨(key.id, val) :: p.values⟩

/-- `Scope(scope, pair::Pair{<:AbstractScopedValue}) = Scope(scope, pair...)`,
`base/scope.jl:38-40`. -/
def mkPair (scope : Option (Scope V)) (pair : Key V × V) : M (Scope V) := mk scope pair.1 pair.2

/-- `Scope(scope, pair1, pair2, pairs...) = Scope(Scope(scope, pair1...), pair2, pairs...)`,
`base/scope.jl:42-46`, unrolled over the pairs after the first. -/
def mkPairs (scope : Option (Scope V)) (pair1 : Key V × V) : List (Key V × V) → M (Scope V)
  | [] => mkPair scope pair1
  | pair2 :: pairs => do
    let s ← mk scope pair1.1 pair1.2
    mkPairs (some s) pair2 pairs

/-- `Scope(::Nothing) = nothing`, `base/scope.jl:47`. -/
def ofNothing : Option (Scope V) := none

/-- The value a list of pairs binds a key to, applied left to right: the last pair
for the key wins; `none` if no pair names the key. -/
def lastFor (k : Nat) : List (Key V × V) → M (Option V)
  | [] => pure none
  | (key, v) :: rest => do
    let w ← key.conv v
    let r ← lastFor k rest
    pure (if r.isSome then r else if key.id == k then some w else none)

/-- A scope built from a parent and pairs looks a key up in the last pair that
binds it, else in the parent; a failed `convert` of any value is thrown; the
other constructors return their argument / `nothing`. -/
def Contract : Prop :=
  (∀ s : Scope V, ofScope s = s) ∧ (@ofNothing V = none) ∧
  (∀ (parent : Option (Scope V)) (key : Key V) (value : V),
    mk parent key value = (key.conv value).map fun w =>
      ⟨(key.id, w) :: (parent.map (·.values)).getD []⟩) ∧
  (∀ (parent : Option (Scope V)) (p1 : Key V × V) (ps : List (Key V × V)) (s : Scope V) (k : Nat),
    mkPairs parent p1 ps = .ok s →
      ∃ last, lastFor k (p1 :: ps) = .ok last ∧
        s.values.get k = (if last.isSome then last else (parent.bind (·.values.get k))))

theorem lastFor_cons (k : Nat) (key : Key V) (v w : V) (rest : List (Key V × V)) (h : key.conv v = .ok w) :
    lastFor k ((key, v) :: rest) = (lastFor k rest).map
      (fun r => if r.isSome then r else if key.id == k then some w else none) := by
  simp only [lastFor, h, bind, Except.bind, pure, Except.pure]
  cases lastFor k rest <;> rfl

theorem mkPairs_spec (k : Nat) : ∀ (ps : List (Key V × V)) (parent : Option (Scope V)) (p1 : Key V × V)
    (s : Scope V), mkPairs parent p1 ps = .ok s →
      ∃ last, lastFor k (p1 :: ps) = .ok last ∧
        s.values.get k = (if last.isSome then last else (parent.bind (·.values.get k))) := by
  intro ps
  induction ps with
  | nil =>
    intro parent p1 s h
    obtain ⟨key, v⟩ := p1
    simp only [mkPairs, mkPair, mk, bind, Except.bind, pure, Except.pure] at h
    cases hc : key.conv v with
    | error e => rw [hc] at h; cases h
    | ok w =>
      rw [hc] at h
      refine ⟨if key.id == k then some w else none, ?_, ?_⟩
      · simp [lastFor, hc, bind, Except.bind, pure, Except.pure]
      · cases parent <;> simp at h <;> subst h <;>
          by_cases hk : key.id = k <;> simp [Storage.get, List.find?, hk]
  | cons p2 ps ih =>
    intro parent p1 s h
    obtain ⟨key, v⟩ := p1
    simp only [mkPairs, mk, bind, Except.bind, pure, Except.pure] at h
    cases hc : key.conv v with
    | error e => rw [hc] at h; cases h
    | ok w =>
      rw [hc] at h
      have h' : mkPairs (some ⟨(key.id, w) :: (parent.map (·.values)).getD []⟩) p2 ps = .ok s := by
        cases parent <;> exact h
      obtain ⟨last, hl, hs⟩ := ih _ _ _ h'
      refine ⟨if last.isSome then last else if key.id == k then some w else none, ?_, ?_⟩
      · rw [lastFor_cons k key v w _ hc, hl]; rfl
      · rw [hs]
        cases last with
        | some x => simp
        | none =>
          cases parent <;> by_cases hk : key.id = k <;> simp [Storage.get, List.find?, hk]

theorem contract_proven : @Contract V := by
  refine ⟨fun _ => rfl, rfl, ?_, fun parent p1 ps s k h => mkPairs_spec k ps parent p1 s h⟩
  intro parent key value
  simp only [mk, bind, Except.bind, pure, Except.pure]
  cases key.conv value <;> cases parent <;> rfl

end Scope

/-! ## `base/baseext.jl` -/

namespace BaseExt

variable {V : Type}

/-- `VecElement{T}(arg) = VecElement{T}(convert(T, arg))`, `base/baseext.jl:17`; the
inner constructor stores the converted value. -/
def vecElement (convT : V → M V) (arg : V) : M V := convT arg

/-- `convert(::Type{T}, arg::T) where {T<:VecElement} = arg`, `base/baseext.jl:18`. -/
def convertSame (arg : V) : M V := .ok arg

/-- `convert(::Type{T}, arg) where {T<:VecElement} = T(arg)::T`, `base/baseext.jl:19`. -/
def convertOther (convT : V → M V) (arg : V) : M V := vecElement convT arg

/-- The `Integer` dimensions given to an `Array` constructor, as integers. -/
abbrev Dims := List Int

/-- `Int(m)` / `convert(Tuple{Vararg{Int}}, d)`: each dimension must fit in `Int`. -/
def toInt (m : Int) : M Int :=
  if -(2 ^ 63) ≤ m ∧ m < 2 ^ 63 then .ok m else .error .inexactError

def toInts : Dims → M (List Int)
  | [] => .ok []
  | m :: ms =>
    match toInt m with
    | .error e => .error e
    | .ok a =>
      match toInts ms with
      | .error e => .error e
      | .ok rest => .ok (a :: rest)

/-- An array: element type tag, dimensions, and elements (`none` is `#undef`). -/
structure Arr (V : Type) where
  eltype : String
  dims : List Int
  elems : List (Option V)

/-- The builtin `Array{T,N}(undef, dims::NTuple{N,Int})`: `ArgumentError` for a
negative dimension or an element count that does not fit (`2^62` here); elements
are uninitialized. -/
def core (T : String) (dims : List Int) : M (Arr V) :=
  if dims.any (· < 0) ∨ dims.foldl (· * ·) 1 ≥ 2 ^ 62 then .error (.argumentError "invalid GenericMemory size")
  else .ok ⟨T, dims, List.replicate (dims.foldl (· * ·) 1).toNat none⟩

/-- `Array{T,N}(::UndefInitializer, d::Vararg{Integer,N})`, `base/baseext.jl:22`; also
`Array{T}(undef, d::Integer...)` (`:27`), `Array{T}(undef, d::NTuple{N,Integer})` (`:32`)
and `Array{T,N}(undef, d::NTuple{N,Integer})` (`:33`): `convert(Tuple{Vararg{Int}}, d)`. -/
def undefN (T : String) (d : Dims) : M (Arr V) := do core T (← toInts d)

/-- `Array{T}(undef, m)` (`:24`), `(undef, m, n)` (`:25`), `(undef, m, n, o)` (`:26`): `Int(m)` each. -/
def undef1 (T : String) (m : Int) : M (Arr V) := do core T [← toInt m]
def undef2 (T : String) (m n : Int) : M (Arr V) := do core T [← toInt m, ← toInt n]
def undef3 (T : String) (m n o : Int) : M (Arr V) := do core T [← toInt m, ← toInt n, ← toInt o]

/-- `Vector(undef, m) = Vector{Any}(undef, Int(m))` (`:29`), `Matrix(undef, m, n)` (`:30`),
`Vector() = Vector{Any}(undef, 0)` (`:35`). -/
def vectorAny (m : Int) : M (Arr V) := undef1 "Any" m
def matrixAny (m n : Int) : M (Arr V) := undef2 "Any" m n
def vector0 : M (Arr V) := undef1 "Any" 0

/-- `fill!(A, x)`: every element becomes `convert(eltype(A), x)`. -/
def fill (convT : V → M V) (A : Arr V) (x : V) : M (Arr V) := do
  let y ← convT x
  pure { A with elems := A.elems.map (fun _ => some y) }

/-- `Array{T,N}(::Nothing, d...)`, `Array{T,N}(::Missing, d...)`, `Array{T}(::Nothing, d...)`,
`Array{T}(::Missing, d...)` (`:39-43`): `fill!(Array{T}(undef, d...), x)` with `x` the
singleton `nothing`/`missing`. -/
def filled (T : String) (convT : V → M V) (x : V) (d : Dims) : M (Arr V) := do
  fill convT (← undefN T d) x

/-- Contract of `base/baseext.jl`: the `VecElement` constructor and conversions store
`convert(T, x)` (and are the identity on a `VecElement{T}`); every `undef` constructor
builds the array of `Int(d)` dimensions with `prod(d)` undefined elements, throwing
`InexactError` exactly when a dimension does not fit in `Int`, and the
`Vector`/`Matrix`/`Vector()` forms have element type `Any`; the `nothing`/`missing`
constructors fill every element with the converted singleton. -/
def Contract : Prop :=
  (∀ (convT : V → M V) (x : V), vecElement convT x = convT x ∧ convertOther convT x = convT x ∧
    convertSame x = .ok x) ∧
  (∀ (T : String) (d : Dims) (A : Arr V), undefN T d = .ok A →
    A.eltype = T ∧ A.dims = d ∧ A.elems.length = (d.foldl (· * ·) 1).toNat ∧ ∀ e ∈ A.elems, e = none) ∧
  (∀ (T : String) (d : Dims), d.any (fun m => !(decide (-(2 ^ 63) ≤ m ∧ m < 2 ^ 63))) →
    (undefN T d : M (Arr V)) = .error .inexactError) ∧
  (∀ (T : String) (m : Int), (undef1 T m : M (Arr V)) = undefN T [m]) ∧
  (∀ (T : String) (m n : Int), (undef2 T m n : M (Arr V)) = undefN T [m, n]) ∧
  (∀ (T : String) (m n o : Int), (undef3 T m n o : M (Arr V)) = undefN T [m, n, o]) ∧
  (∀ m : Int, (vectorAny m : M (Arr V)) = undefN "Any" [m]) ∧
  (∀ m n : Int, (matrixAny m n : M (Arr V)) = undefN "Any" [m, n]) ∧
  ((vector0 : M (Arr V)).map (fun A => (A.eltype, A.dims, A.elems.length)) = .ok ("Any", [0], 0)) ∧
  (∀ (T : String) (convT : V → M V) (x : V) (d : Dims) (A : Arr V),
    filled T convT x d = .ok A → ∃ y, convT x = .ok y ∧ A.dims = d ∧ ∀ e ∈ A.elems, e = some y)

theorem toInts_ok : ∀ (d : Dims) (l : List Int), toInts d = .ok l → l = d := by
  intro d
  induction d with
  | nil => intro l h; simp only [toInts, Except.ok.injEq] at h; exact h.symm
  | cons m ms ih =>
    intro l h
    simp only [toInts] at h
    cases hm : toInt m with
    | error e => rw [hm] at h; cases h
    | ok a =>
      rw [hm] at h
      cases hr : toInts ms with
      | error e => rw [hr] at h; cases h
      | ok rest =>
        rw [hr] at h
        cases h
        have ha : a = m := by
          simp only [toInt] at hm
          split at hm
          · cases hm; rfl
          · cases hm
        rw [ha, ih rest hr]

theorem toInts_err : ∀ (d : Dims), d.any (fun m => !(decide (-(2 ^ 63) ≤ m ∧ m < 2 ^ 63))) →
    toInts d = .error .inexactError := by
  intro d
  induction d with
  | nil => intro h; simp at h
  | cons m ms ih =>
    intro h
    simp only [toInts]
    by_cases hm : -(2 ^ 63) ≤ m ∧ m < 2 ^ 63
    · have ht : toInt m = .ok m := by simp only [toInt]; rw [if_pos hm]
      rw [ht]
      have h' : ms.any (fun m => !(decide (-(2 ^ 63) ≤ m ∧ m < 2 ^ 63))) := by
        simp only [List.any_cons, hm, decide_true, Bool.not_true, Bool.false_or] at h
        exact h
      rw [ih h']
    · have ht : toInt m = .error .inexactError := by simp only [toInt]; rw [if_neg hm]
      rw [ht]

theorem undef1_eq (T : String) (m : Int) : (undef1 T m : M (Arr V)) = undefN T [m] := by
  simp only [undef1, undefN, toInts, bind, Except.bind, pure, Except.pure]
  cases toInt m <;> rfl

theorem undef2_eq (T : String) (m n : Int) : (undef2 T m n : M (Arr V)) = undefN T [m, n] := by
  simp only [undef2, undefN, toInts, bind, Except.bind, pure, Except.pure]
  cases toInt m <;> cases toInt n <;> rfl

theorem undef3_eq (T : String) (m n o : Int) : (undef3 T m n o : M (Arr V)) = undefN T [m, n, o] := by
  simp only [undef3, undefN, toInts, bind, Except.bind, pure, Except.pure]
  cases toInt m <;> cases toInt n <;> cases toInt o <;> rfl

theorem contract_proven : @Contract V := by
  refine ⟨fun _ _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, undef1_eq, undef2_eq, undef3_eq,
    fun m => undef1_eq "Any" m, fun m n => undef2_eq "Any" m n, rfl, ?_⟩
  · intro T d A h
    simp only [undefN, bind, Except.bind] at h
    cases hd : toInts d with
    | error e => rw [hd] at h; cases h
    | ok l =>
      rw [hd] at h
      have := toInts_ok d l hd
      subst this
      simp only [core] at h
      split at h
      · cases h
      · cases h
        refine ⟨rfl, rfl, by simp, ?_⟩
        intro e he
        exact (List.eq_of_mem_replicate he)
  · intro T d h
    simp only [undefN, bind, Except.bind, toInts_err d h]
  · intro T convT x d A h
    simp only [filled, fill, bind, Except.bind, pure, Except.pure] at h
    cases hu : (undefN T d : M (Arr V)) with
    | error e => rw [hu] at h; cases h
    | ok B =>
      rw [hu] at h
      cases hc : convT x with
      | error e => rw [hc] at h; cases h
      | ok y =>
        rw [hc] at h
        cases h
        refine ⟨y, rfl, ?_, ?_⟩
        · simp only [undefN, bind, Except.bind] at hu
          cases hd : toInts d with
          | error e => rw [hd] at hu; cases hu
          | ok l =>
            rw [hd] at hu
            have := toInts_ok d l hd
            subst this
            simp only [core] at hu
            split at hu
            · cases hu
            · cases hu; rfl
        · intro e he
          simp only [List.mem_map] at he
          obtain ⟨_, _, h⟩ := he
          exact h.symm

end BaseExt

end JuliaLean.MiscCov
