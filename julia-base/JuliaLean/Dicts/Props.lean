import JuliaLean.Dicts.Ops
import JuliaLean.Float.Basic

/-!
# Properties of `Dict` and `Set`

Each property holds for every hash function and every `isequal` satisfying
the documented contract (`KeyOps.Lawful`), including hashes where all keys
collide. "Reachable" tables are those built from `Dict()` by a small sequence
of API calls (`Reach`).
-/

namespace JuliaLean.Dicts

/-- Both calls throw the same exception, or both return results related by `R`. -/
def SameOutcome {α β : Type} (A : DR α) (B : DR β) (R : α → β → Prop) : Prop :=
  match A, B with
  | .ok a, .ok b => R a b
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

/-! ## Dict -/

/-- Every small call sequence from `Dict()`, including `get!` with a `default`
that mutates the dictionary, gives the reference result: the same exception,
or a table that agrees with the reference map (lookups, iteration yields each
key exactly once, `length` counts the distinct keys). -/
def OpsAgree : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ ops : List (DOp K V), OpsSmall ops → SameOutcome (runOps o ops) (rrun o ops) (Agrees o)

/-- `d[k] = v` stores `v` under `k`; a later lookup of any key `isequal` to `k`
finds `v`, other keys are unaffected. -/
def SetindexLookup : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ k v, ∃ t', setindex o t v k = .ok t' ∧
    Agrees o t' (rset o m k v) ∧
    ∀ q, dictGet o t' q = .ok (if o.eq q k then some v else rlookup o m q)

/-- `delete!(d, k)` removes `k` (lookups of keys `isequal` to `k` miss) and nothing else. -/
def DeleteLookup : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ k, ∃ t', dictDelete o t k = .ok t' ∧
    Agrees o t' (rdel o m k) ∧
    ∀ q, dictGet o t' q = .ok (if o.eq q k then none else rlookup o m q)

/-- `pop!(d, k)` returns the value and deletes the key, or throws `KeyError`;
`pop!(d, k, default)` returns `default` instead of throwing. -/
def PopKeyAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ k (dflt : V),
    (match rfind o m k with
     | some (_, w) => ∃ t', popKey o t k = .ok (w, t') ∧ Agrees o t' (rdel o m k)
     | none => popKey o t k = .error .keyError) ∧
    (∃ t', popKeyDefault o t k dflt = .ok ((rlookup o m k).getD dflt, t') ∧
      Agrees o t' (rdel o m k))

/-- `get!(d, k, v)` returns the stored value, or stores and returns `v`. -/
def GetBangValueAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ k v,
    match rfind o m k with
    | some (_, w) => ∃ t', getBangVal o t k v = .ok (w, t') ∧ Agrees o t' m
    | none => ∃ t', getBangVal o t k v = .ok (v, t') ∧ Agrees o t' (rset o m k v)

/-- `get!(f, d, k)` where `f()` itself inserts, deletes, rehashes, merges or
empties `d` (`base/dict.jl:462-468` re-probes when `h.age` changed): when `k`
is present `f` is not called; otherwise the result is `f()`'s value, stored
under `k` on top of everything `f` left in `d`. -/
def GetBangMutatingDefault : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ k v (inner : List (BaseOp K V)), InnerSmall inner →
    match rfind o m k, getBang o t k (innerDefault o v inner) with
    | some (_, w), .ok (r, t') => r = w ∧ Agrees o t' m
    | none, .ok (r, t') => r = v ∧ ∃ m', rbaseList o m inner = .ok m' ∧ Agrees o t' (rset o m' k v)
    | none, .error e => rbaseList o m inner = .error e
    | _, _ => False

/-- `sizehint!(d, n; shrink)` for hints with `3n` within `Int` keeps the contents. -/
def SizehintSmallAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ (n : JInt .i64) shrink, n.val ≤ 2 ^ 61 →
    ∃ t', sizehint o t n shrink = .ok t' ∧ Agrees o t' m

/-- `sizehint!(d, n; shrink)` returns, keeping the contents, for every `n`: it
"suggest[s] that collection `s` reserve capacity for at least `n` elements"
(`base/array.jl:1584`). -/
def SizehintAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ (n : JInt .i64) shrink,
    ∃ t', sizehint o t n shrink = .ok t' ∧ Agrees o t' m

/-- `empty!(d)` leaves no entries. -/
def EmptyAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → Agrees o (emptyBang t) []

/-- `filter!(pred, d)` keeps exactly the pairs satisfying `pred`, even when all keys collide. -/
def FilterAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ pred : K → V → Bool,
    ∃ t', filterBang t pred = .ok t' ∧ Agrees o t' (m.filter fun e => pred e.1 e.2)

/-- `merge!(d, d2)` and `mergewith!(f, d, d2)` give the reference union. -/
def MergeAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ (ps : List (K × V)) (f : V → V → V), ps.length ≤ 2 ^ 30 →
    ∃ d2, buildDict o ps = .ok d2 ∧
      (∃ t', dictMerge o t d2 = .ok t' ∧
        Agrees o t' ((rbuild o ps).foldl (fun m kv => rset o m kv.1 kv.2) m)) ∧
      (∃ t', mergewith o f t d2 = .ok t' ∧ Agrees o t' ((rbuild o ps).foldl (rcombine o f) m))

/-- `pop!(d)` removes and returns some stored pair; it throws `ArgumentError` on an empty dict. -/
def PopAnyAgrees : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m →
    match m with
    | [] => popAny t = .error .argumentError
    | _ :: _ => ∃ k v t', popAny t = .ok ((k, v), t') ∧ (k, v) ∈ m ∧ Agrees o t' (rdel o m k)

/-- `Float64` keys compared with `isequal` and any hash consistent with it. -/
def f64Ops (h : Float.F64 → JInt .u64) : KeyOps Float.F64 := { hash := h, eq := Float.F64.isequal }

/-- Keys are compared with `isequal` (`Dict` docstring, `base/dict.jl:35`; `Set`
docstring examples `base/set.jl:30-36`): storing `y` after `x` overwrites `x`
exactly when `isequal(x, y)`, so every NaN is the same key while `0.0` and
`-0.0` are two keys. -/
def FloatKeysIsequal : Prop :=
  ∀ (h : Float.F64 → JInt .u64), (∀ a b, Float.F64.isequal a b = true → h a = h b) →
  ∀ (V : Type) (t : Table Float.F64 V) m, Reach (f64Ops h) t m → ∀ (x y : Float.F64) (v w : V),
    ∃ t₁ t₂, setindex (f64Ops h) t v x = .ok t₁ ∧ setindex (f64Ops h) t₁ w y = .ok t₂ ∧
      dictGet (f64Ops h) t₂ x = .ok (some (if Float.F64.isequal x y then w else v)) ∧
      dictGet (f64Ops h) t₂ y = .ok (some w) ∧
      dictLength t₂ = (rset (f64Ops h) (rset (f64Ops h) m x v) y w).length

/-! ## Set -/

/-- Membership in a reference set. -/
def rmem {K : Type} (o : KeyOps K) (m : RMap K Unit) (x : K) : Bool := (rfind o m x).isSome

/-- The generic key type: `max_values(K) = typemax(Int)`. -/
def GenericMax {K : Type} (o : KeyOps K) : Prop := o.maxValues = JInt.typemax .i64

/-- `union!(s, t)`: membership is `x ∈ s || x ∈ t`, and `s` agrees with the reference union. -/
def SetUnionAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', unionSet o s t = .ok s' ∧
      Agrees o s' (mt.foldl (fun m e => rset o m e.1 ()) ms) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x || rmem o mt x)

/-- `intersect!(s, t)`: membership is `x ∈ s && x ∈ t`. -/
def SetIntersectAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', intersectBang o s t = .ok s' ∧
      Agrees o s' (ms.filter fun e => rmem o mt e.1) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x && rmem o mt x)

/-- `setdiff!(s, t)` (both branches of `base/set.jl:187-198`): membership is `x ∈ s && x ∉ t`. -/
def SetSetdiffAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', setdiffBang o s t = .ok s' ∧
      Agrees o s' (ms.filter fun e => !rmem o mt e.1) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x && !rmem o mt x)

/-- `symdiff!(s, t)`: membership is `x ∈ s` xor `x ∈ t`. -/
def SetSymdiffAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', symdiffBang o s t = .ok s' ∧
      Agrees o s' (mt.foldl (fun m e => if rmem o m e.1 then rdel o m e.1 else rset o m e.1 ()) ms) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x != rmem o mt x)

/-- `issubset(s, t)` and `s == t` decide inclusion and equality of the member sets. -/
def SetCompareAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    issubsetSet o s t = .ok (ms.all fun e => rmem o mt e.1) ∧
    setEq o s t = .ok (ms.all (fun e => rmem o mt e.1) && mt.all (fun e => rmem o ms e.1))

/-- Conversions consistent with `hash`/`isequal` (`base/hashing.jl:12-16`), and
`convert(K, x) === x` for `x isa K`. -/
structure ConvLawful {Q K : Type} (o : KeyOps K) (c : Conv Q K) : Prop where
  hash_eq : ∀ q k, c.iseq q k = true → c.hash q = o.hash k
  iseq_eq : ∀ q k k', c.iseq q k = true → o.eq k k' = true → c.iseq q k' = true
  isa_convert : ∀ q k, c.isa q = some k → c.convert q = .ok k ∧ c.iseq q k = true

/-- `in!(x, s)` is `in(x, s) ? true : (push!(s, x); false)` (docstring `base/set.jl:94-100`). -/
def InBangEquiv : Prop :=
  ∀ (K Q : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → ConvLawful o c → GenericMax o →
  ∀ (s : SetT K) ms, Reach o s ms → ∀ x : Q,
    SameOutcome (inBang o c s x)
      (do if ← inConv c s x then pure (true, s) else do
            let s ← pushConv o c s x
            pure (false, s) : DR (Bool × SetT K))
      (fun r₁ r₂ => r₁.1 = r₂.1 ∧ ∀ y, setIn o r₁.2 y = setIn o r₂.2 y)

/-- `union!(s, itr)` (and `Set{T}(itr)`) has the outcome of pushing every element
of `itr` in turn: the same exception, or the same members. -/
def UnionPushEquiv : Prop :=
  ∀ (K Q : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → ConvLawful o c → MaxValuesOK o →
  ∀ (s : SetT K) ms, Reach o s ms → ∀ itr : List Q, itr.length ≤ 2 ^ 30 →
    SameOutcome (unionBang o c s itr) (itr.foldlM (pushConv o c) s)
      (fun s₁ s₂ => ∀ y, setIn o s₁ y = setIn o s₂ y)

/-- `issubset(a, b)` for vectors "determine[s] whether every element of `a` is
also in `b`, using `in`" (`base/abstractset.jl:315`), and `in` on a vector uses `==`. -/
def IssubsetVecUsesIn : Prop :=
  ∀ (E : Type) (o : KeyOps E) (eqeq : E → E → Bool), o.Lawful → GenericMax o →
  (∀ a b, eqeq a b = eqeq b a) →
  ∀ a b : List E, issubsetVec o eqeq a b = .ok (a.all fun x => b.any fun y => eqeq y x)

end JuliaLean.Dicts
