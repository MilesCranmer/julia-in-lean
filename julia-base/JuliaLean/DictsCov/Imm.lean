import JuliaLean.DictsCov.AbsModel
import JuliaLean.Dicts.Immutable

/-!
# `ImmutableDict`, `base/dict.jl:776-892` (master `bbfa0ce4150`)

An `ImmutableDict{K,V}` is its chain of pairs, most recent first
(`JuliaLean.Dicts.IDict`). `new(parent, key, value)` converts `key` to `K` and
`value` to `V` (the field types); those conversions are `ck` and `cv`. A
lookup key of type `Q` meets stored keys through `eq k q`, which is
`isequal(dict.key, key)`.
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

variable {K V Q W : Type}

/-- `ImmutableDict{K,V}() = new()`, `base/dict.jl:780`. -/
def immNew : IDict K V := []

/-- `ImmutableDict{K,V}(key, value) = (empty = new(); new(empty, key, value))`, `base/dict.jl:781`. -/
def immNew2 (ck : Q → DR K) (cv : W → DR V) (key : Q) (value : W) : DR (IDict K V) := do
  let k ← ck key
  let v ← cv value
  pure [(k, v)]

/-- `ImmutableDict{K,V}(parent::ImmutableDict, key, value) = new(parent, key, value)`, `base/dict.jl:782`. -/
def immNew3 (ck : Q → DR K) (cv : W → DR V) (parent : IDict K V) (key : Q) (value : W) :
    DR (IDict K V) := do
  let k ← ck key
  let v ← cv value
  pure ((k, v) :: parent)

/-- `ImmutableDict(KV::Pair{K,V}) = ImmutableDict{K,V}(KV[1], KV[2])`, `base/dict.jl:811`
(the pair already has the field types). -/
def immOfPair (kv : K × V) : DR (IDict K V) := immNew2 pure pure kv.1 kv.2

/-- `ImmutableDict(t::ImmutableDict{K,V}, KV::Pair) = ImmutableDict{K,V}(t, KV[1], KV[2])`,
`base/dict.jl:812`. -/
def immPush (ck : Q → DR K) (cv : W → DR V) (t : IDict K V) (kv : Q × W) : DR (IDict K V) :=
  immNew3 ck cv t kv.1 kv.2

/-- `ImmutableDict(t::ImmutableDict{K,V}, KV::Pair, rest::Pair...) =
ImmutableDict(ImmutableDict(t, KV), rest...)`, `base/dict.jl:813-814`. -/
def immPushMany (ck : Q → DR K) (cv : W → DR V) (t : IDict K V) (kv : Q × W) :
    List (Q × W) → DR (IDict K V)
  | [] => immPush ck cv t kv
  | r :: rest => do
    let t ← immPush ck cv t kv
    immPushMany ck cv t r rest

/-- `ImmutableDict(KV::Pair, rest::Pair...) = ImmutableDict(ImmutableDict(KV), rest...)`,
`base/dict.jl:815`. -/
def immOfPairs (ck : Q → DR K) (cv : W → DR V) (kv : K × V) : List (Q × W) → DR (IDict K V)
  | [] => immOfPair kv
  | r :: rest => do
    let t ← immOfPair kv
    immPushMany ck cv t r rest

/-- `haskey(dict::ImmutableDict, key)`, `base/dict.jl:828-834`. -/
def immHaskey (eq : K → Q → Bool) : IDict K V → Q → Bool
  | [], _ => false
  | (k, _) :: parent, key => if eq k key then true else immHaskey eq parent key

/-- `getindex(dict::ImmutableDict, key)`, `base/dict.jl:836-842`. -/
def immGetindex (eq : K → Q → Bool) : IDict K V → Q → DR V
  | [], _ => throw .keyError
  | (k, v) :: parent, key => if eq k key then pure v else immGetindex eq parent key

/-- `get(dict::ImmutableDict, key, default)`, `base/dict.jl:843-849`. -/
def immGet (eq : K → Q → Bool) : IDict K V → Q → V → V
  | [], _, default => default
  | (k, v) :: parent, key, default => if eq k key then v else immGet eq parent key default

/-- `get(default::Callable, dict::ImmutableDict, key)`, `base/dict.jl:851-857`. -/
def immGetF (eq : K → Q → Bool) : IDict K V → Q → (Unit → DR V) → DR V
  | [], _, default => default ()
  | (k, v) :: parent, key, default => if eq k key then pure v else immGetF eq parent key default

/-- `iterate(d::ImmutableDict{K,V}, t=d)`, `base/dict.jl:860-863`. -/
def immIterate (t : IDict K V) : Option ((K × V) × IDict K V) :=
  match t with
  | [] => none
  | (k, v) :: parent => some ((k, v), parent)

/-- `for pair in t` to exhaustion through `immIterate`. -/
def immCollect : IDict K V → List (K × V)
  | [] => []
  | e :: parent => match immIterate (e :: parent) with
    | none => []
    | some (p, _) => p :: immCollect parent

/-- `length(t::ImmutableDict) = count(Returns(true), t)`, `base/dict.jl:864`. -/
def immLength (t : IDict K V) : Nat := ((immCollect t).filter fun _ => true).length

/-- `isempty(t::ImmutableDict) = !isdefined(t, :parent)`, `base/dict.jl:865`. -/
def immIsempty (t : IDict K V) : Bool := t.isEmpty

/-- `empty(::ImmutableDict, ::Type{K}, ::Type{V}) = ImmutableDict{K,V}()`, `base/dict.jl:866`. -/
def immEmpty (_ : IDict K V) : IDict K V := immNew

/-- The message of `_similar_for(c::AbstractDict, ::Type{T}, ...)`, `base/dict.jl:891-892`. -/
def similarMsg : String :=
  "for AbstractDicts, similar requires an element type of Pair;\n  if calling map, consider a comprehension instead"

/-- `_similar_for(c::AbstractDict, ::Type{Pair{K,V}}, itr, isz, len) = empty(c, K, V)` and
`_similar_for(c::AbstractDict, ::Type{T}, ...) = throw(ArgumentError(...))`,
`base/dict.jl:890-892`: `pairParams T` is `some (K, V)` for `T = Pair{K,V}`. -/
def similarFor {T D K' V' : Type} (ops : DictOps T D K' V') (c : D) (pairParams : Option (T × T)) : GR D :=
  match pairParams with
  | some (k, v) => pure (ops.emptyT c k v)
  | none => throw (.argumentError similarMsg)

/-- The chain after converting the pairs `ps`, most recent first. -/
def convChain (ck : Q → DR K) (cv : W → DR V) (ps : List (Q × W)) : DR (List (K × V)) :=
  ps.foldlM (fun acc p => do
    let k ← ck p.1
    let v ← cv p.2
    pure ((k, v) :: acc)) []

/-- `ImmutableDict` docstring (`base/dict.jl:784-809`): the constructors store
every pair, most recent first, converting to `K` and `V`; lookups (`haskey`,
`getindex`, `get`, `get(f, ...)`) return the most recent value of an
`isequal` key; iteration yields every pair from most recent to least recent;
`length` counts them, `isempty` tests for none, `empty` has none, and
`_similar_for` builds an empty dictionary only for a `Pair` element type. -/
def ImmutableDictSpec : Prop :=
  ∀ (K V Q W : Type) (ck : Q → DR K) (cv : W → DR V) (eq : K → Q → Bool),
    (∀ (t : IDict K V) (key : Q),
      immHaskey eq t key = t.any (fun e => eq e.1 key) ∧
      immGetindex eq t key = (match t.find? (fun e => eq e.1 key) with
        | some e => .ok e.2 | none => .error .keyError) ∧
      (∀ default : V, immGet eq t key default =
        match t.find? (fun e => eq e.1 key) with | some e => e.2 | none => default) ∧
      (∀ default : Unit → DR V, immGetF eq t key default =
        match t.find? (fun e => eq e.1 key) with | some e => .ok e.2 | none => default ())) ∧
    (∀ t : IDict K V, immIterate t = (match t with | [] => none | e :: p => some (e, p)) ∧
      immCollect t = t ∧ immLength t = t.length ∧ (immIsempty t = true ↔ t = []) ∧ immEmpty t = []) ∧
    immNew (K := K) (V := V) = [] ∧
    (∀ (t : IDict K V) (key : Q) (value : W),
      immNew2 ck cv key value = (do let k ← ck key; let v ← cv value; pure [(k, v)]) ∧
      immNew3 ck cv t key value = (do let k ← ck key; let v ← cv value; pure ((k, v) :: t))) ∧
    (∀ kv : K × V, immOfPair kv = .ok [kv]) ∧
    (∀ (t : IDict K V) (kv : Q × W) (rest : List (Q × W)),
      immPushMany ck cv t kv rest = (do let c ← convChain ck cv (kv :: rest); pure (c ++ t))) ∧
    (∀ (kv : K × V) (rest : List (Q × W)),
      immOfPairs ck cv kv rest = (do let c ← convChain ck cv rest; pure (c ++ [kv]))) ∧
    (∀ (T D K' V' : Type) (ops : DictOps T D K' V') (c : D) (k v : T),
      similarFor ops c (some (k, v)) = .ok (ops.emptyT c k v) ∧
      similarFor ops c none = .error (.argumentError similarMsg))

theorem convChain_cons_acc (ck : Q → DR K) (cv : W → DR V) :
    ∀ (ps : List (Q × W)) (acc : List (K × V)),
      ps.foldlM (fun acc p => do
        let k ← ck p.1
        let v ← cv p.2
        pure ((k, v) :: acc)) acc =
      (do let c ← convChain ck cv ps; pure (c ++ acc))
  | [], acc => rfl
  | p :: ps, acc => by
    unfold convChain
    simp only [List.foldlM_cons]
    cases hk : ck p.1 with
    | error e => rfl
    | ok k =>
      cases hv : cv p.2 with
      | error e => rfl
      | ok v =>
        show List.foldlM _ ((k, v) :: acc) ps = (List.foldlM _ [(k, v)] ps >>= fun c => pure (c ++ acc))
        rw [convChain_cons_acc ck cv ps ((k, v) :: acc), convChain_cons_acc ck cv ps [(k, v)]]
        cases convChain ck cv ps with
        | error e => rfl
        | ok c => show Except.ok (c ++ (k, v) :: acc) = Except.ok ((c ++ [(k, v)]) ++ acc); simp

theorem immPushMany_eq (ck : Q → DR K) (cv : W → DR V) :
    ∀ (t : IDict K V) (kv : Q × W) (rest : List (Q × W)),
      immPushMany ck cv t kv rest = (do let c ← convChain ck cv (kv :: rest); pure (c ++ t))
  | t, kv, [] => by
    show immNew3 ck cv t kv.1 kv.2 = _
    unfold immNew3 convChain
    simp only [List.foldlM_cons, List.foldlM_nil]
    cases ck kv.1 <;> try rfl
    cases cv kv.2 <;> rfl
  | t, kv, r :: rest => by
    show (immNew3 ck cv t kv.1 kv.2 >>= fun t => immPushMany ck cv t r rest) = _
    rw [convChain, List.foldlM_cons]
    unfold immNew3
    cases hk : ck kv.1 with
    | error e => rfl
    | ok k =>
      cases hv : cv kv.2 with
      | error e => rfl
      | ok v =>
        show immPushMany ck cv ((k, v) :: t) r rest = List.foldlM _ [(k, v)] (r :: rest) >>= _
        rw [immPushMany_eq ck cv ((k, v) :: t) r rest, convChain_cons_acc ck cv (r :: rest) [(k, v)]]
        cases convChain ck cv (r :: rest) with
        | error e => rfl
        | ok c => show Except.ok (c ++ (k, v) :: t) = Except.ok ((c ++ [(k, v)]) ++ t); simp

theorem immCollect_eq : ∀ t : IDict K V, immCollect t = t
  | [] => rfl
  | (k, v) :: p => by
    show (k, v) :: immCollect p = _
    rw [immCollect_eq p]

theorem immutableDictSpec_proven : ImmutableDictSpec := by
  intro K V Q W ck cv eq
  refine ⟨fun t key => ⟨?_, ?_, fun default => ?_, fun default => ?_⟩, fun t => ⟨?_, immCollect_eq t,
    ?_, ?_, rfl⟩, rfl, fun t key value => ⟨rfl, rfl⟩, fun kv => rfl,
    fun t kv rest => immPushMany_eq ck cv t kv rest, fun kv rest => ?_,
    fun T D K' V' ops c k v => ⟨rfl, rfl⟩⟩
  · induction t with
    | nil => rfl
    | cons e p ih =>
      obtain ⟨k, v⟩ := e
      simp only [immHaskey, List.any_cons]
      cases eq k key <;> simp [ih]
  · induction t with
    | nil => rfl
    | cons e p ih =>
      obtain ⟨k, v⟩ := e
      simp only [immGetindex]
      cases h : eq k key
      · rw [List.find?_cons_of_neg (by simp [h])]; simpa using ih
      · rw [List.find?_cons_of_pos (by simpa using h)]; rfl
  · induction t with
    | nil => rfl
    | cons e p ih =>
      obtain ⟨k, v⟩ := e
      simp only [immGet]
      cases h : eq k key
      · rw [List.find?_cons_of_neg (by simp [h])]; simpa using ih
      · rw [List.find?_cons_of_pos (by simpa using h)]; rfl
  · induction t with
    | nil => rfl
    | cons e p ih =>
      obtain ⟨k, v⟩ := e
      simp only [immGetF]
      cases h : eq k key
      · rw [List.find?_cons_of_neg (by simp [h])]; simpa using ih
      · rw [List.find?_cons_of_pos (by simpa using h)]; rfl
  · cases t with
    | nil => rfl
    | cons e p => obtain ⟨k, v⟩ := e; rfl
  · unfold immLength; rw [immCollect_eq]; simp
  · unfold immIsempty; cases t <;> simp
  · cases rest with
    | nil => show immOfPair kv = _; rfl
    | cons r rest =>
      show immPushMany ck cv [kv] r rest = _
      rw [immPushMany_eq]
      rfl

end JuliaLean.DictsCov
