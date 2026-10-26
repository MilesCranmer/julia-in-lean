import JuliaLean.SortTuplesCov.Common

/-!
Model of `base/ordering.jl` (module `Base.Order`, master `bbfa0ce4150`).

Orderings compare values of a universe `V`. `isl` is `isless` on `V`; `idx`
reads the `Integer` value of an argument of `lt(::Perm, a, b)`. A Julia
vector is the `List V` of its elements, indexed from 1; `eltypeOf` gives the
element type of a vector and `typeOf` the type of a value, both opaque.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds)

/-- The `Ordering` structs of `base/ordering.jl:29-108`: `ForwardOrdering()`,
`ReverseOrdering{Fwd}(fwd)`, `By(by, order)`, `Lt(lt)` and `Perm(order, data)`. -/
inductive Ordering (V : Type) where
  | forward
  | rev (fwd : Ordering V)
  | by (f : V → V) (order : Ordering V)
  | ltf (f : V → V → Bool)
  | perm (order : Ordering V) (data : List V)

namespace Ordering

variable {V : Type}

/-- `ReverseOrdering(x)`: `ReverseOrdering(rev::ReverseOrdering) = rev.fwd`
(`base/ordering.jl:46`), `ReverseOrdering(by::By) = By(by.by, ReverseOrdering(by.order))`
(`:110`), `ReverseOrdering(perm::Perm) = Perm(ReverseOrdering(perm.order), perm.data)`
(`:111`), and otherwise `ReverseOrdering{Fwd}(fwd)` (`:47`). -/
def reverseOrdering : Ordering V → Ordering V
  | .rev fwd => fwd
  | .by f o => .by f (reverseOrdering o)
  | .perm o d => .perm (reverseOrdering o) d
  | .forward => .rev .forward
  | .ltf f => .rev (.ltf f)

/-- `ReverseOrdering() = ReverseOrdering(ForwardOrdering())`, `base/ordering.jl:48`;
this is the constant `Reverse` (`:72`). -/
def reverseDefault : Ordering V := reverseOrdering .forward

/-- `reverse(o::Ordering) = ReverseOrdering(o)`, `base/ordering.jl:56`. -/
def reverse (o : Ordering V) : Ordering V := reverseOrdering o

/-- `By(by) = By(by, Forward)`, `base/ordering.jl:86`. -/
def byDefault (f : V → V) : Ordering V := .by f .forward

/-- `lt(o, a, b)`, `base/ordering.jl:118-127`. The `Perm` method reads
`p.data[a]` and `p.data[b]` with bounds checking, evaluates both comparisons
(non-short-circuit `|` and `&`), and breaks ties by `a < b`. -/
def lt (isl : V → V → Bool) (idx : V → Int) : Ordering V → V → V → R Bool
  | .forward, a, b => .ok (isl a b)
  | .rev fwd, a, b => lt isl idx fwd b a
  | .by f o, a, b => lt isl idx o (f a) (f b)
  | .ltf f, a, b => .ok (f a b)
  | .perm o d, a, b => do
    let da ← getfield d (idx a)
    let db ← getfield d (idx b)
    let x ← lt isl idx o da db
    let y ← lt isl idx o db da
    pure (x || (!y && decide (idx a < idx b)))

/-- The `lt` keyword of `ord`: the function `isless` itself, or any other function. -/
inductive LtArg (V : Type) where
  | isless
  | fn (f : V → V → Bool)

/-- The `by` keyword of `ord`: the function `identity` itself, or any other function. -/
inductive ByArg (V : Type) where
  | identity
  | fn (f : V → V)

/-- `_by(by, order) = By(by, order)`, `_by(::typeof(identity), order) = order`,
`base/ordering.jl:136-137`. -/
def by_ (b : ByArg V) (o : Ordering V) : Ordering V :=
  match b with
  | .identity => o
  | .fn f => .by f o

/-- `_ord(lt, by, order)`, `base/ordering.jl:130-135`: with `lt === isless` the
order is kept (`:130-132`); otherwise `Forward` becomes `Lt(lt)` (`:133`),
`ReverseOrdering{ForwardOrdering}` becomes `reverse(_by(by, Lt(lt)))` (`:134`),
and every other order throws `ErrorException` (`:135`). -/
def ord_ (l : LtArg V) (b : ByArg V) (o : Ordering V) : R (Ordering V) :=
  match l, o with
  | .isless, o => .ok (by_ b o)
  | .fn f, .forward => .ok (by_ b (.ltf f))
  | .fn f, .rev .forward => .ok (reverse (by_ b (.ltf f)))
  | .fn _, _ => .error .errorException

/-- `ord(lt, by, rev::Nothing, order) = _ord(lt, by, order)` (`base/ordering.jl:155`)
and `ord(lt, by, rev::Bool, order)`, which reverses when `rev` (`:157-160`). -/
def ord (l : LtArg V) (b : ByArg V) (rev : Option Bool) (o : Ordering V) : R (Ordering V) :=
  match rev with
  | none => ord_ l b o
  | some r => do
    let o' ← ord_ l b o
    pure (if r then reverseOrdering o' else o')

/-- `ordtype(o, vs)`, `base/ordering.jl:170-174`. `vs[1]` of an empty vector
throws, which the `try` turns into `Any`. -/
def ordtype {T : Type} (typeOf : V → T) (eltypeOf : List V → T) (anyT : T) :
    Ordering V → List V → T
  | .rev fwd, vs => ordtype typeOf eltypeOf anyT fwd vs
  | .perm o d, _ => ordtype typeOf eltypeOf anyT o d
  | .by f _, vs => match vs with
    | [] => anyT
    | x :: _ => typeOf (f x)
  | .forward, vs => eltypeOf vs
  | .ltf _, vs => eltypeOf vs

/-- The order contains no `Perm`. -/
def noPerm : Ordering V → Bool
  | .forward => true
  | .rev o => noPerm o
  | .by _ o => noPerm o
  | .ltf _ => true
  | .perm _ _ => false

/-- The order is built by the outer constructors of `base/ordering.jl`: a
`ReverseOrdering` wraps only `Forward` or an `Lt` (the methods of lines 46,
110 and 111 never build `ReverseOrdering{<:ReverseOrdering}`, `{<:By}` or
`{<:Perm}`; only an explicit type parameter does). -/
def normal : Ordering V → Bool
  | .forward => true
  | .rev .forward => true
  | .rev (.ltf _) => true
  | .rev _ => false
  | .by _ o => normal o
  | .ltf _ => true
  | .perm o _ => normal o

/-- `lt` of an order without `Perm` never throws: its value. -/
def ltv (isl : V → V → Bool) : Ordering V → V → V → Bool
  | .forward, a, b => isl a b
  | .rev fwd, a, b => ltv isl fwd b a
  | .by f o, a, b => ltv isl o (f a) (f b)
  | .ltf f, a, b => f a b
  | .perm o _, a, b => ltv isl o a b

end Ordering

open Ordering

variable {V : Type}

/-! ## Properties -/

/-- `ReverseOrdering` docstring, `base/ordering.jl:33-41`: for every ordering
`o` and all `a`, `b`, `lt(ReverseOrdering(o), a, b) == lt(o, b, a)`. -/
def ReverseOrderingLtSwap : Prop :=
  ∀ (V : Type) (isl : V → V → Bool) (idx : V → Int) (o : Ordering V) (a b : V),
    lt isl idx (reverseOrdering o) a b = lt isl idx o b a

/-- The constructors of `ReverseOrdering` and `reverse(o)` for orderings
without `Perm` (`base/ordering.jl:46-48,56,110`): `ReverseOrdering(o)` swaps the
arguments of `lt`, reversing twice restores every ordering built by the outer
constructors, `Reverse` compares by
`isless` with swapped arguments, and `By(f)` compares `f` values by `isless`. -/
def ReverseOrderingCorrect : Prop :=
  ∀ (V : Type) (isl : V → V → Bool) (idx : V → Int),
    (∀ (o : Ordering V), noPerm o = true → ∀ a b,
      lt isl idx (reverseOrdering o) a b = lt isl idx o b a ∧
      lt isl idx (reverse o) a b = lt isl idx o b a ∧
      lt isl idx o a b = .ok (ltv isl o a b)) ∧
    (∀ (o : Ordering V), normal o = true →
      normal (reverseOrdering o) = true ∧ reverseOrdering (reverseOrdering o) = o) ∧
    (∀ a b, lt isl idx (reverseDefault : Ordering V) a b = .ok (isl b a)) ∧
    (∀ (f : V → V) a b, lt isl idx (byDefault f) a b = .ok (isl (f a) (f b)))

/-- `lt` is a strict weak order on the values of `V` (`sort!` docstring). -/
structure Swo {V : Type} (lt : V → V → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  ntrans : ∀ a b c, lt a b = false → lt b c = false → lt a c = false

/-- `Perm` docstring, `base/ordering.jl:98-103`: for valid indices `i`, `j`,
`lt(Perm(order, data), i, j)` is true when `data[i]` is less than `data[j]`,
false when `data[j]` is less than `data[i]`, and otherwise `i < j`; an
index outside the data throws `BoundsError`. For an underlying strict weak
order, `Perm` is a strict weak order on valid indices that is total (two
distinct indices always compare). -/
def PermLtCorrect : Prop :=
  ∀ (V : Type) (isl : V → V → Bool) (idx : V → Int) (o : Ordering V) (d : List V),
    noPerm o = true →
    (∀ a b, 1 ≤ idx a → idx a ≤ d.length → 1 ≤ idx b → idx b ≤ d.length →
      ∃ da db, d[(idx a - 1).toNat]? = some da ∧ d[(idx b - 1).toNat]? = some db ∧
        lt isl idx (.perm o d) a b =
          .ok (if ltv isl o da db then true else if ltv isl o db da then false
               else decide (idx a < idx b))) ∧
    (∀ a b, ¬ (1 ≤ idx a ∧ idx a ≤ d.length) → lt isl idx (.perm o d) a b = bounds) ∧
    (Swo (ltv isl o) → ∀ a b,
      1 ≤ idx a → idx a ≤ d.length → 1 ≤ idx b → idx b ≤ d.length →
      lt isl idx (.perm o d) a a = .ok false ∧
      (idx a ≠ idx b → (lt isl idx (.perm o d) a b = .ok true ∨ lt isl idx (.perm o d) b a = .ok true)) ∧
      ¬ (lt isl idx (.perm o d) a b = .ok true ∧ lt isl idx (.perm o d) b a = .ok true))

/-- `Lt(lt)` calls `lt`, `By(by, order)` compares `by` values with `order`,
and `Forward` is `isless` (`base/ordering.jl:74-96,118-121`). -/
def LtMethodsCorrect : Prop :=
  ∀ (V : Type) (isl : V → V → Bool) (idx : V → Int) (a b : V),
    lt isl idx .forward a b = .ok (isl a b) ∧
    (∀ f, lt isl idx (.ltf f) a b = .ok (f a b)) ∧
    (∀ f (o : Ordering V), lt isl idx (.by f o) a b = lt isl idx o (f a) (f b)) ∧
    (∀ (o : Ordering V), lt isl idx (.rev o) a b = lt isl idx o b a)

/-- The comparison `ord` promises before `rev` (`base/ordering.jl:139-153`):
keys are `by` values; they are compared with `lt`, or with the given order
when `lt` is `isless`. A custom `lt` with `order = Reverse` compares swapped keys. -/
def ordSpec0 {V : Type} (isl : V → V → Bool) (idx : V → Int) (l : LtArg V) (b : ByArg V)
    (o : Ordering V) (x y : V) : R Bool :=
  let k : V → V := match b with | .identity => id | .fn f => f
  match l with
  | .isless => lt isl idx o (k x) (k y)
  | .fn f => match o with
    | .forward => .ok (f (k x) (k y))
    | _ => .ok (f (k y) (k x))

/-- `ordSpec0`, with the arguments swapped when `rev == true` ("the resulting
order is reversed if `rev=true`"). -/
def ordSpec {V : Type} (isl : V → V → Bool) (idx : V → Int) (l : LtArg V) (b : ByArg V)
    (rev : Option Bool) (o : Ordering V) (x y : V) : R Bool :=
  if rev = some true then ordSpec0 isl idx l b o y x else ordSpec0 isl idx l b o x y

/-- `ord(lt, by, rev, order)` (`base/ordering.jl:139-160`): for `lt = isless`
every order (without `Perm`) is accepted; for another `lt` the orders `Forward`
and `Reverse` are accepted; an accepted result compares as `ordSpec`. -/
def OrdCorrect : Prop :=
  ∀ (V : Type) (isl : V → V → Bool) (idx : V → Int) (l : LtArg V) (b : ByArg V)
    (rev : Option Bool) (o : Ordering V), noPerm o = true →
    (match l, o with
     | .fn _, .forward => True
     | .fn _, .rev .forward => True
     | .isless, _ => True
     | .fn _, _ => False) →
    ∃ o', ord l b rev o = .ok o' ∧ ∀ x y, lt isl idx o' x y = ordSpec isl idx l b rev o x y

/-- `ord` rejects a custom `lt` with any order other than `Forward` and
`Reverse` with `ErrorException`, `base/ordering.jl:135,150-151`. -/
def OrdRejects : Prop :=
  ∀ (V : Type) (f : V → V → Bool) (b : ByArg V) (rev : Option Bool) (o : Ordering V),
    o ≠ .forward → o ≠ .rev .forward → ord (.fn f) b rev o = .error .errorException

/-- `ordtype(o, vs)` (`base/ordering.jl:170-174`): the element type for direct
orders, the type of `by(vs[1])` for `By` (`Any` for an empty `vs`), the
`ordtype` of the wrapped order for `ReverseOrdering`, and of `data` for
`Perm`; reversing an order never changes its `ordtype`. -/
def OrdtypeCorrect : Prop :=
  ∀ (V T : Type) (typeOf : V → T) (eltypeOf : List V → T) (anyT : T),
    (∀ vs, ordtype typeOf eltypeOf anyT (.forward : Ordering V) vs = eltypeOf vs) ∧
    (∀ f vs, ordtype typeOf eltypeOf anyT (.ltf f : Ordering V) vs = eltypeOf vs) ∧
    (∀ (f : V → V) (o : Ordering V) x vs, ordtype typeOf eltypeOf anyT (.by f o) (x :: vs) = typeOf (f x)) ∧
    (∀ (f : V → V) (o : Ordering V), ordtype typeOf eltypeOf anyT (.by f o) [] = anyT) ∧
    (∀ (o : Ordering V) d vs, ordtype typeOf eltypeOf anyT (.perm o d) vs = ordtype typeOf eltypeOf anyT o d) ∧
    (∀ (o : Ordering V) vs,
      ordtype typeOf eltypeOf anyT (reverseOrdering o) vs = ordtype typeOf eltypeOf anyT o vs)

/-! ## Proofs -/

theorem lt_noPerm (isl : V → V → Bool) (idx : V → Int) :
    ∀ (o : Ordering V), noPerm o = true → ∀ a b, lt isl idx o a b = .ok (ltv isl o a b)
  | .forward, _, a, b => rfl
  | .rev o, h, a, b => by simp only [lt, ltv]; exact lt_noPerm isl idx o h b a
  | .by f o, h, a, b => by simp only [lt, ltv]; exact lt_noPerm isl idx o h _ _
  | .ltf f, _, a, b => rfl
  | .perm _ _, h, _, _ => by simp [noPerm] at h

theorem noPerm_reverseOrdering : ∀ (o : Ordering V), noPerm o = true → noPerm (reverseOrdering o) = true
  | .forward, _ => rfl
  | .rev o, h => by simpa [reverseOrdering, noPerm] using h
  | .by f o, h => by simp only [reverseOrdering, noPerm]; exact noPerm_reverseOrdering o h
  | .ltf f, _ => rfl
  | .perm _ _, h => by simp [noPerm] at h

theorem ltv_reverseOrdering (isl : V → V → Bool) :
    ∀ (o : Ordering V), noPerm o = true → ∀ a b, ltv isl (reverseOrdering o) a b = ltv isl o b a
  | .forward, _, a, b => rfl
  | .rev o, _, a, b => rfl
  | .by f o, h, a, b => by
    simp only [reverseOrdering, ltv]; exact ltv_reverseOrdering isl o h _ _
  | .ltf f, _, a, b => rfl
  | .perm _ _, h, _, _ => by simp [noPerm] at h

theorem normal_reverseOrdering : ∀ (o : Ordering V), normal o = true → normal (reverseOrdering o) = true
  | .forward, _ => rfl
  | .rev .forward, _ => rfl
  | .rev (.ltf _), _ => rfl
  | .rev (.rev _), h => by simp [normal] at h
  | .rev (.by _ _), h => by simp [normal] at h
  | .rev (.perm _ _), h => by simp [normal] at h
  | .by f o, h => by simp only [reverseOrdering, normal] at h ⊢; exact normal_reverseOrdering o h
  | .ltf _, _ => rfl
  | .perm o d, h => by simp only [reverseOrdering, normal] at h ⊢; exact normal_reverseOrdering o h

theorem reverseOrdering_involutive : ∀ (o : Ordering V), normal o = true →
    reverseOrdering (reverseOrdering o) = o
  | .forward, _ => rfl
  | .rev .forward, _ => rfl
  | .rev (.ltf _), _ => rfl
  | .rev (.rev _), h => by simp [normal] at h
  | .rev (.by _ _), h => by simp [normal] at h
  | .rev (.perm _ _), h => by simp [normal] at h
  | .by f o, h => by
    simp only [normal] at h
    simp [reverseOrdering, reverseOrdering_involutive o h]
  | .ltf _, _ => rfl
  | .perm o d, h => by
    simp only [normal] at h
    simp [reverseOrdering, reverseOrdering_involutive o h]

theorem reverseOrderingCorrect : ReverseOrderingCorrect := by
  intro V isl idx
  refine ⟨?_, fun o h => ⟨normal_reverseOrdering o h, reverseOrdering_involutive o h⟩,
    fun a b => rfl, fun f a b => rfl⟩
  intro o h a b
  have h1 : lt isl idx (reverseOrdering o) a b = lt isl idx o b a := by
    rw [lt_noPerm isl idx _ (noPerm_reverseOrdering o h), lt_noPerm isl idx o h,
      ltv_reverseOrdering isl o h]
  exact ⟨h1, h1, lt_noPerm isl idx o h a b⟩

/-- `ReverseOrdering(Perm(Forward, [0, 0]))` keeps the ascending tie-breaker:
`lt(ReverseOrdering(p), 1, 2)` is `true` but `lt(p, 2, 1)` is `false`. -/
theorem reverseOrderingLtSwap_refuted : ¬ ReverseOrderingLtSwap := by
  intro h
  have := h Int (fun a b => decide (a < b)) id (.perm .forward [0, 0]) 1 2
  have e1 : lt (fun a b => decide (a < b)) id
      (reverseOrdering (Ordering.perm .forward [0, 0] : Ordering Int)) 1 2 = .ok true := rfl
  have e2 : lt (fun a b => decide (a < b)) id
      (Ordering.perm .forward [0, 0] : Ordering Int) 2 1 = .ok false := rfl
  rw [e1, e2] at this
  cases this

theorem permLtCorrect : PermLtCorrect := by
  intro V isl idx o d hnp
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha1 ha2 hb1 hb2
    obtain ⟨da, hda, hga⟩ := getfield_some (d := d) ha1 ha2
    obtain ⟨db, hdb, hgb⟩ := getfield_some (d := d) hb1 hb2
    refine ⟨da, db, hda, hdb, ?_⟩
    simp only [lt, hga, hgb, lt_noPerm isl idx o hnp, bind, Except.bind, pure, Except.pure]
    cases ltv isl o da db <;> cases ltv isl o db da <;> rfl
  · intro a b ha
    simp only [lt]
    rw [getfield_none ha]
    rfl
  · intro hs a b ha1 ha2 hb1 hb2
    obtain ⟨da, hda, hga⟩ := getfield_some (d := d) ha1 ha2
    obtain ⟨db, hdb, hgb⟩ := getfield_some (d := d) hb1 hb2
    have e : ∀ x y : V, ∀ u v : Int, ∀ gx gy,
        getfield d u = .ok gx → getfield d v = .ok gy → gx = x → gy = y →
        ∀ a' b' : V, idx a' = u → idx b' = v →
        lt isl idx (.perm o d) a' b' = .ok (ltv isl o x y || (!ltv isl o y x && decide (u < v))) := by
      intro x y u v gx gy hu hv hx hy a' b' ha' hb'
      subst hx hy
      simp only [lt, ha', hb', hu, hv, lt_noPerm isl idx o hnp, bind, Except.bind, pure, Except.pure]
    have hab := e da db (idx a) (idx b) da db hga hgb rfl rfl a b rfl rfl
    have hba := e db da (idx b) (idx a) db da hgb hga rfl rfl b a rfl rfl
    have haa := e da da (idx a) (idx a) da da hga hga rfl rfl a a rfl rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [haa, hs.irrefl]; simp
    · intro hne
      rw [hab, hba]
      cases h1 : ltv isl o da db <;> cases h2 : ltv isl o db da <;> simp <;> omega
    · rw [hab, hba]
      intro ⟨h1, h2⟩
      simp only [Except.ok.injEq] at h1 h2
      cases h3 : ltv isl o da db <;> cases h4 : ltv isl o db da <;> simp [h3, h4] at h1 h2
      · omega
      · have := hs.trans _ _ _ h3 h4; rw [hs.irrefl] at this; cases this

theorem ltMethodsCorrect : LtMethodsCorrect := by
  intro V isl idx a b
  exact ⟨rfl, fun f => rfl, fun f o => rfl, fun o => rfl⟩

theorem lt_rev_noPerm (isl : V → V → Bool) (idx : V → Int) (o : Ordering V) (h : noPerm o = true)
    (a b : V) : lt isl idx (reverseOrdering o) a b = lt isl idx o b a := by
  rw [lt_noPerm isl idx _ (noPerm_reverseOrdering o h), lt_noPerm isl idx o h,
    ltv_reverseOrdering isl o h]

theorem noPerm_by (b : ByArg V) (o : Ordering V) (h : noPerm o = true) : noPerm (by_ b o) = true := by
  cases b <;> simpa [by_, noPerm] using h

theorem ord_base (isl : V → V → Bool) (idx : V → Int) (l : LtArg V) (b : ByArg V)
    (o : Ordering V)
    (hok : match l, o with
     | .fn _, .forward => True
     | .fn _, .rev .forward => True
     | .isless, _ => True
     | .fn _, _ => False) (hnp : noPerm o = true) :
    ∃ o', ord_ l b o = .ok o' ∧ noPerm o' = true ∧
      ∀ x y, lt isl idx o' x y = ordSpec0 isl idx l b o x y := by
  cases l with
  | isless =>
    refine ⟨by_ b o, rfl, noPerm_by b o hnp, fun x y => ?_⟩
    cases b <;> rfl
  | fn f =>
    cases o with
    | forward =>
      refine ⟨by_ b (.ltf f), rfl, noPerm_by b _ rfl, fun x y => ?_⟩
      cases b <;> rfl
    | rev o2 =>
      cases o2 with
      | forward =>
        refine ⟨reverse (by_ b (.ltf f)), rfl, noPerm_reverseOrdering _ (noPerm_by b _ rfl),
          fun x y => ?_⟩
        cases b <;> rfl
      | rev _ => cases hok
      | «by» _ _ => cases hok
      | ltf _ => cases hok
      | perm _ _ => cases hok
    | «by» _ _ => cases hok
    | ltf _ => cases hok
    | perm _ _ => cases hok

theorem ordCorrect : OrdCorrect := by
  intro V isl idx l b rev o hnp hok
  obtain ⟨o', h1, h2, h3⟩ := ord_base isl idx l b o hok hnp
  cases rev with
  | none => exact ⟨o', by simp [ord, h1], fun x y => by simp [ordSpec, h3]⟩
  | some r =>
    cases r with
    | false =>
      refine ⟨o', by simp [ord, h1, bind, Except.bind, pure, Except.pure], fun x y => ?_⟩
      simp [ordSpec, h3]
    | true =>
      refine ⟨reverseOrdering o', by simp [ord, h1, bind, Except.bind, pure, Except.pure],
        fun x y => ?_⟩
      rw [lt_rev_noPerm isl idx o' h2, h3]
      simp [ordSpec]

theorem ordRejects : OrdRejects := by
  intro V f b rev o h1 h2
  have base : ord_ (.fn f) b o = .error .errorException := by
    cases o with
    | forward => exact absurd rfl h1
    | rev o2 =>
      cases o2 with
      | forward => exact absurd rfl h2
      | rev _ => rfl
      | «by» _ _ => rfl
      | ltf _ => rfl
      | perm _ _ => rfl
    | «by» _ _ => rfl
    | ltf _ => rfl
    | perm _ _ => rfl
  cases rev with
  | none => exact base
  | some r => simp [ord, base, bind, Except.bind]

theorem ordtype_reverseOrdering {T : Type} (typeOf : V → T) (eltypeOf : List V → T) (anyT : T) :
    ∀ (o : Ordering V) vs,
      ordtype typeOf eltypeOf anyT (reverseOrdering o) vs = ordtype typeOf eltypeOf anyT o vs
  | .forward, _ => rfl
  | .rev _, _ => rfl
  | .by _ _, vs => by cases vs <;> rfl
  | .ltf _, _ => rfl
  | .perm o d, _ => by simp only [reverseOrdering, ordtype]; exact ordtype_reverseOrdering _ _ _ o d

theorem ordtypeCorrect : OrdtypeCorrect := by
  intro V T typeOf eltypeOf anyT
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    ordtype_reverseOrdering typeOf eltypeOf anyT⟩

end JuliaLean.SortTuplesCov
