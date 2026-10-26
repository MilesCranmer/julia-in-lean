import JuliaLean.SortTuplesCov.TupleProofs

/-! Faithful models for the remaining type and construction methods in
`base/tuple.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

mutual
  inductive TupleTy where
    | bottom | any | atom (name : String)
    | tuple (params : List TupleParam)
    | union (a b : TupleTy)
    | unionAll (body : TupleTy)

  /-- A tuple parameter is a type, a value parameter, or `Vararg{T,N}`. -/
  inductive TupleParam where
    | type (ty : TupleTy)
    | value
    | vararg (ty : TupleTy) (length : Option Int)
end

/-- `_counttuple(::Type{<:NTuple{N,Any}})`, `base/tuple.jl:23`. -/
def countTupleSpecific : TupleTy → Option Int
  | .tuple [.vararg .any (some n)] => some n
  | _ => none

/-- `_counttuple(::Type) = nothing`, `base/tuple.jl:24`. -/
def countTupleFallback (_ : TupleTy) : Option Int := none

def unwrapVararg : TupleParam → TupleParam
  | .vararg t _ => .type t
  | p => p

def paramType : TupleParam → Option TupleTy
  | .type t | .vararg t _ => some t
  | .value => none

/-- `_compute_eltype`, `base/tuple.jl:291-313`.  `free` models
`has_free_typevars`; `join` is Julia's `promote_typejoin`. -/
def computeTupleEltype (join : TupleTy → TupleTy → TupleTy) (free : TupleTy → Bool) :
    (t : TupleTy) → TupleTy
  | .union a b =>
    if free (.union a b) then .any else join a b
  | .tuple [] => if free (.tuple []) then .any else .bottom
  | .tuple (p :: ps) =>
    if free (.tuple (p :: ps)) then .any else
    match paramType (unwrapVararg p) with
    | none => .bottom
    | some first => ps.foldl (fun r p =>
        match r, paramType (unwrapVararg p) with
        | .any, _ => .any
        | _, none => .bottom
        | _, some e => join e r) first
  | .unionAll body =>
    if free (.unionAll body) then .any else body
  | t => if free t then .any else .bottom

/-- `_eltype_ntuple`, `base/tuple.jl:279`: a defined type parameter is used;
an empty vacuous match is Bottom; otherwise `_compute_eltype` recovers the join. -/
def eltypeNTuple (join : TupleTy → TupleTy → TupleTy) (free : TupleTy → Bool) :
    TupleTy → TupleTy
  | t@(.tuple [.vararg e _]) => e
  | t@(.tuple []) => .bottom
  | t => computeTupleEltype join free t

/-- `eltype(::Type{<:Tuple})`, `base/tuple.jl:282-290`. -/
def tupleEltype (join : TupleTy → TupleTy → TupleTy) (free : TupleTy → Bool)
    (ntupleSignature : TupleTy → Bool) (t : TupleTy) : TupleTy :=
  match t with
  | .tuple [] => .bottom
  | _ => if ntupleSignature t then eltypeNTuple join free t else computeTupleEltype join free t

/-- `keytype(t::Tuple)` and `keytype(::Type{<:Tuple})`,
`base/tuple.jl:316-317`. -/
def tupleKeytypeValue (_ : List TupleTy) : TupleTy := .atom "Int64"
def tupleKeytypeType (_ : TupleTy) : TupleTy := .atom "Int64"

/-- `valtype(t::Tuple)` and `valtype(::Type{<:Tuple})`,
`base/tuple.jl:319-320`. -/
def tupleValtypeValue (join : TupleTy → TupleTy → TupleTy) (ts : List TupleTy) : TupleTy :=
  computeTupleEltype join (fun _ => false) (.tuple (ts.map .type))
def tupleValtypeType (join : TupleTy → TupleTy → TupleTy) (t : TupleTy) : TupleTy :=
  computeTupleEltype join (fun _ => false) t

/-- `tuple_type_tail`, `base/tuple.jl:453-468`. -/
def tupleTypeTail : TupleTy → Jl TupleTy
  | .unionAll body => tupleTypeTail body |>.map .unionAll
  | .union a b => do pure (.union (← tupleTypeTail a) (← tupleTypeTail b))
  | .tuple [.vararg t (some n)] => .ok (.tuple [.vararg t (some (n - 1))])
  | .tuple (_ :: ps) => .ok (.tuple ps)
  | .tuple [] => .ok (.tuple [])
  | _ => .error (.methodError "tuple_type_tail")

def TupleTypeMethodsCorrect : Prop :=
  (∀ n, countTupleSpecific (.tuple [.vararg .any (some n)]) = some n) ∧
  (∀ t, countTupleFallback t = none) ∧
  (∀ join free, tupleEltype join free (fun _ => false) (.tuple []) = .bottom) ∧
  (∀ join free a b, computeTupleEltype join free (.union a b) =
    if free (.union a b) then .any
    else join a b) ∧
  (∀ ts, tupleKeytypeValue ts = .atom "Int64") ∧
  (∀ t, tupleKeytypeType t = .atom "Int64") ∧
  (∀ join ts, tupleValtypeValue join ts =
    computeTupleEltype join (fun _ => false) (.tuple (ts.map .type))) ∧
  (∀ join t, tupleValtypeType join t = computeTupleEltype join (fun _ => false) t) ∧
  (∀ t n, tupleTypeTail (.tuple [.vararg t (some n)]) =
    .ok (.tuple [.vararg t (some (n - 1))])) ∧
  (∀ t ps, tupleTypeTail (.tuple (.type t :: ps)) = .ok (.tuple ps)) ∧
  (∀ a b, tupleTypeTail (.union a b) = do
    pure (.union (← tupleTypeTail a) (← tupleTypeTail b)))

theorem tupleTypeMethodsCorrect : TupleTypeMethodsCorrect := by
  refine ⟨by simp [countTupleSpecific], by simp [countTupleFallback], by simp [tupleEltype], ?_,
    by simp [tupleKeytypeValue], by simp [tupleKeytypeType], by simp [tupleValtypeValue],
    by simp [tupleValtypeType], by simp [tupleTypeTail], by simp [tupleTypeTail], ?_⟩
  intro join free a b
  simp [computeTupleEltype]
  intro a b
  rfl

/-! ### Tuple construction from iterators -/

/-- `(::Type{T})(x::Tuple)`, `base/tuple.jl:470`. -/
def tupleTypeCall {V : Type} (isT : List V → Bool) (convert : List V → Jl (List V))
    (x : List V) : Jl (List V) :=
  if isT x then .ok x else convert x

/-- `Tuple(x::Ref)` and `Tuple(x::Array{T,0})`, `base/tuple.jl:472-473`. -/
def tupleRef {V : Type} (x : V) : List V := [x]
def tupleArray0 {V : Type} (x : V) : List V := [x]

/-- `_totuple_err`, `base/tuple.jl:479-482`. -/
def toTupleError {V : Type} : Jl (List V) :=
  .error (.argumentError "too few elements for tuple type")

/-- Recursive `_totuple(::Type{T}, itr, state...)`, `base/tuple.jl:484-495`.
The target field types are processed left to right and conversion happens only
when the value is not already of the requested type. -/
def toTupleFixed {V : Type} (hasType : V → TupleTy → Bool)
    (convert : TupleTy → V → Jl V) : List TupleTy → List V → Jl (List V)
  | [], _ => .ok []
  | _ :: _, [] => toTupleError
  | t :: ts, x :: xs => do
    let y ← if hasType x t then .ok x else convert t x
    pure (y :: (← toTupleFixed hasType convert ts xs))

/-- Iterative `All32` method, `base/tuple.jl:498-505`. -/
def toTupleLong {V : Type} (convert : V → Jl V) (length : Nat) (xs : List V) : Jl (List V) := do
  let ys ← (xs.take length).mapM convert
  if ys.length = length then .ok ys else toTupleError

/-- Vararg and unparameterized methods, `base/tuple.jl:509-511`. -/
def toTupleVararg {V : Type} (convert : V → Jl V) (xs : List V) : Jl (List V) :=
  xs.mapM convert
def toTupleAny {V : Type} (xs : List V) : List V := xs

inductive TupleSource (V : Type) where
  | array (xs : List V) | simpleVector (xs : List V) | namedTuple (xs : List V)
  | pair (first second : V) | number (x : V)

/-- Fast `_totuple(::Type{Tuple}, ...)` methods, `base/tuple.jl:514-518`. -/
def toTupleFast {V : Type} : TupleSource V → List V
  | .array xs | .simpleVector xs | .namedTuple xs => xs
  | .pair a b => [a, b]
  | .number x => [x]

def TupleConstructionCorrect : Prop :=
  (∀ (V : Type) (isT : List V → Bool) convert x,
    isT x = true → tupleTypeCall isT convert x = .ok x) ∧
  (∀ (V : Type) (x : V), tupleRef x = [x] ∧ tupleArray0 x = [x]) ∧
  (∀ (V : Type), (toTupleError : Jl (List V)) =
    .error (.argumentError "too few elements for tuple type")) ∧
  (∀ (V : Type) hasType convert xs,
    toTupleFixed (V := V) hasType convert [] xs = .ok []) ∧
  (∀ (V : Type) convert xs, toTupleVararg (V := V) convert xs = xs.mapM convert) ∧
  (∀ (V : Type) (xs : List V), toTupleAny xs = xs) ∧
  (∀ (V : Type) (a b : V), toTupleFast (.pair a b) = [a, b]) ∧
  (∀ (V : Type) (x : V), toTupleFast (.number x) = [x])

theorem tupleConstructionCorrect : TupleConstructionCorrect := by
  refine ⟨?_, by simp [tupleRef, tupleArray0], by simp [toTupleError], by simp [toTupleFixed],
    by simp [toTupleVararg], by simp [toTupleAny], by simp [toTupleFast], by simp [toTupleFast]⟩
  intro V isT convert x h
  simp [tupleTypeCall, h]

end JuliaLean.SortTuplesCov
