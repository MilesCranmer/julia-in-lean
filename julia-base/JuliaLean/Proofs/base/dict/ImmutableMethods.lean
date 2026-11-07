import JuliaLean.base.dict
import JuliaLean.base.abstractdict

namespace JuliaLean.DictsCov
open JuliaLean.Dicts
variable {K V Q W : Type}


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
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
        change immPushMany ck cv ((k, v) :: t) r rest =
          (do
            let c ← (r :: rest).foldlM (fun acc p => do
              let k ← ck p.1
              let v ← cv p.2
              pure ((k, v) :: acc)) [(k, v)]
            pure (c ++ t))
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

end JuliaLean.DictsCov
