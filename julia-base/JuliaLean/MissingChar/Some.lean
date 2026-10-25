import JuliaLean.MissingChar.Basic

/-!
# `coalesce`, `something`, `Some`, `notnothing`: `base/missing.jl`, `base/some.jl`

Values are `JV α`: `missing`, `nothing`, `Some(v)` for any value `v` (so
`Some(nothing)` and `Some(Some(x))` exist), or an ordinary value of type `α`.
-/

namespace JuliaLean.MissingChar

inductive JV (α : Type) where
  | missing
  | nothing
  | some (v : JV α)
  | val (a : α)
  deriving Repr

/-- `ismissing(x) = x === missing`, `base/essentials.jl`. -/
def JV.isMissing : JV α → Bool
  | .missing => true
  | _ => false

/-- `isnothing(x) = x === nothing`, `base/some.jl:67`. -/
def JV.isNothing : JV α → Bool
  | .nothing => true
  | _ => false

/-- `coalesce(x...)`, `base/missing.jl:420-422`:
`coalesce() = missing`, `coalesce(x::Missing, y...) = coalesce(y...)`,
`coalesce(x::Any, y...) = x`. -/
def coalesce : List (JV α) → JV α
  | [] => .missing
  | .missing :: ys => coalesce ys
  | x :: _ => x

/-- `something(x...)`, `base/some.jl:99-102`. -/
def something : List (JV α) → Jl (JV α)
  | [] => .error (.argumentError "No value arguments present")
  | .nothing :: ys => something ys
  | .some v :: _ => .ok v
  | x :: _ => .ok x

/-- `@coalesce(x...)`, `base/missing.jl:451-457`: arguments evaluated in turn,
`!ismissing(val) ? val : <rest>`, innermost `missing`. -/
def atCoalesce : List (JV α) → JV α
  | [] => .missing
  | v :: rest => if !v.isMissing then v else atCoalesce rest

/-- `@something(x...)`, `base/some.jl:138-167`: the first value that is not
`nothing` is passed to `something(val)`; the innermost expression is
`something(nothing)`. -/
def atSomething : List (JV α) → Jl (JV α)
  | [] => something [.nothing]
  | v :: rest => if !v.isNothing then something [v] else atSomething rest

/-- `notnothing(x)`, `base/some.jl:54-55`. -/
def notnothing : JV α → Jl (JV α)
  | .nothing => .error (.argumentError "nothing passed to notnothing")
  | x => .ok x

/-- `coalesce` docstring, `base/missing.jl:398-399`: "Return the first value in the
arguments which is not equal to `missing`, if any. Otherwise return `missing`."
The short-circuiting `@coalesce` returns the same value. -/
def CoalesceFirst : Prop :=
  ∀ (α : Type) (xs : List (JV α)),
    coalesce xs = ((xs.find? (fun x => !x.isMissing)).getD .missing) ∧ atCoalesce xs = coalesce xs

theorem coalesceFirst_proven : CoalesceFirst := by
  intro α xs
  induction xs with
  | nil => simp [coalesce, atCoalesce]
  | cons x xs ih =>
    cases x <;> simp_all [coalesce, atCoalesce, JV.isMissing]

/-- `something` docstring, `base/some.jl:73-75`: "Return the first value in the
arguments which is not equal to `nothing`, if any. Otherwise throw an error.
Arguments of type `Some` are unwrapped." The short-circuiting `@something`
gives the same result. -/
def SomethingFirst : Prop :=
  ∀ (α : Type) (xs : List (JV α)),
    something xs = (match xs.find? (fun x => !x.isNothing) with
      | none => .error (.argumentError "No value arguments present")
      | some (.some v) => .ok v
      | some x => .ok x) ∧
    atSomething xs = something xs

theorem somethingFirst_proven : SomethingFirst := by
  intro α xs
  induction xs with
  | nil => simp [something, atSomething]
  | cons x xs ih =>
    cases x <;> simp_all [something, atSomething, JV.isNothing]

/-- `notnothing` docstring, `base/some.jl:50-52`: "Throw an error if `x === nothing`,
and return `x` if not." -/
def NotnothingSpec : Prop :=
  ∀ (α : Type) (x : JV α), (x.isNothing = true → ∃ e, notnothing x = .error e) ∧
    (x.isNothing = false → notnothing x = .ok x)

theorem notnothingSpec_proven : NotnothingSpec := by
  intro α x
  cases x <;> simp [notnothing, JV.isNothing]

/-! ## `Some` equality and hashing, `base/some.jl:169-172` -/

/-- `isequal(a::Some, b::Some) = isequal(a.value, b.value)`, `base/some.jl:170`. -/
def isequalSome (eqv : α → α → Bool) (a b : α) : Bool := eqv a b

/-- `hash(s::Some, h) = hash(s.value, hash_some_seed +% h)`, `base/some.jl:171-172`. -/
def hashSome (hash : α → UInt64 → UInt64) (a : α) (h : UInt64) : UInt64 :=
  hash a (0xde5c997007a4ca3a + h)

/-- The `hash` contract (`isequal(x, y)` implies `hash(x) == hash(y)`) carries over
to `Some` wrappers whenever it holds for the wrapped values. -/
def SomeHashIsequal : Prop :=
  ∀ (α : Type) (eqv : α → α → Bool) (hash : α → UInt64 → UInt64),
    (∀ a b h, eqv a b = true → hash a h = hash b h) →
    ∀ a b h, isequalSome eqv a b = true → hashSome hash a h = hashSome hash b h

theorem someHashIsequal_proven : SomeHashIsequal := by
  intro α eqv hash hc a b h e
  exact hc a b _ e

/-! ## `show` of a vector of `Some{Int64}` and evaluating the printed text -/

/-- The printed form of an expression, as Julia code. -/
inductive Printed where
  /-- An integer literal. -/
  | int (n : Int)
  /-- `Some(<arg>)`. -/
  | someCall (arg : Printed)
  /-- `Some{Int64}[<elems>]`, a typed vector literal. -/
  | someVec (elems : List Printed)
  deriving Repr

/-- The values involved: `Int64` integers and `Some{Int64}` wrappers. -/
inductive SV where
  | int (n : Int)
  | some (n : Int)
  deriving Repr, DecidableEq

/-- `show(io, x::Some)`, `base/some.jl:39-47`: the bare value when the context's
`:typeinfo` is `typeof(x)`, else `Some(<value>)`. `typeinfoIsSome` is
`get(io, :typeinfo, Any) == Some{Int64}`. -/
def showSome (typeinfoIsSome : Bool) (n : Int) : Printed :=
  if typeinfoIsSome then .int n else .someCall (.int n)

/-- `show(io, v::Vector{Some{Int64}})` via `show_vector`, `base/arrayshow.jl:540-558`:
`typeinfo_prefix` (`:595-`) prints `Some{Int64}` (the eltype is not implicit, since
`Some{Int64}` is not a singleton type), and the elements are shown with
`:typeinfo => eltype(v)`. -/
def showSomeVec (v : List Int) : Printed := .someVec (v.map (showSome true))

/-- Evaluating printed code. `T[a, b]` converts each element to `T`; there is
`convert(::Type{Some{T}}, x::Some)` (`base/some.jl:36-37`) but no method converting an
`Int64` to `Some{Int64}`, so that is a `MethodError`. -/
def evalP : Printed → Jl SV
  | .int n => .ok (.int n)
  | .someCall a => do
    match ← evalP a with
    | .int n => .ok (.some n)
    | .some _ => .error (.methodError "Some{Int64}(::Some)")
  | .someVec _ => .error (.methodError "vector in scalar position")

/-- Evaluating `Some{Int64}[e1, e2, ...]`: each element is evaluated and converted. -/
def evalSomeVec : Printed → Jl (List Int)
  | .someVec es => es.mapM fun e => do
    match ← evalP e with
    | .some n => .ok n
    | .int _ => .error (.methodError "convert(::Type{Some{Int64}}, ::Int64)")
  | _ => .error (.methodError "not a vector literal")

/-- The `show` docstring (`base/show.jl`): the printed form "should be parseable
Julia code when possible"; for a `Vector{Some{Int64}}` evaluating it should give
the vector back. -/
def SomeShowEval : Prop :=
  ∀ v : List Int, evalSomeVec (showSomeVec v) = .ok v

theorem someShowEval_refuted : ¬ SomeShowEval := by
  intro h
  have := h [1]
  revert this
  decide

/-! ## `sincos`, `sincosd`, `sincospi` of `missing` -/

/-- Results of the tuple-valued trigonometric functions: a 2-tuple of values that
may be missing, or a bare `missing`. -/
inductive Trig (F : Type) where
  | missing
  | tuple (s c : Option F)

/-- `sincos(x)`: `sincos(x) = _sincos(float(x))` (`base/special/trig.jl:205`),
`float(::Missing) = missing` (`base/missing.jl:96-103`),
`_sincos(x) = (sin(x), cos(x))` (`:203`) and `sin(::Missing) = cos(::Missing) =
missing` (`base/math.jl:1322-1332`). `k` is the Float64 kernel. -/
def sincos (k : F → F × F) : Option F → Trig F
  | none => .tuple none none
  | some x => .tuple (some (k x).1) (some (k x).2)

/-- `sincosd(::Missing) = (missing, missing)`, `base/special/trig.jl:1547`. -/
def sincosd (k : F → F × F) : Option F → Trig F
  | none => .tuple none none
  | some x => .tuple (some (k x).1) (some (k x).2)

/-- `sincospi(::Missing) = missing` from the loop at `base/math.jl:1322-1332`. -/
def sincospi (k : F → F × F) : Option F → Trig F
  | none => .missing
  | some x => .tuple (some (k x).1) (some (k x).2)

/-- `sincos`, `sincosd` and `sincospi` return a tuple `(sine, cosine)`
(`base/special/trig.jl:993-996`), and missing propagates into both components
(doc/src/manual/missing.md:14-18). -/
def SincosFamilyMissing : Prop :=
  ∀ (F : Type) (k : F → F × F) (x : Option F),
    ∀ f ∈ [sincos k, sincosd k, sincospi k], ∃ s c, f x = .tuple s c ∧ (x = none → s = none ∧ c = none)

theorem sincosFamilyMissing_refuted : ¬ SincosFamilyMissing := by
  intro h
  obtain ⟨s, c, hf, -⟩ := h Unit (fun _ => ((), ())) none (sincospi fun _ => ((), ()))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
  simp [sincospi] at hf

end JuliaLean.MissingChar
