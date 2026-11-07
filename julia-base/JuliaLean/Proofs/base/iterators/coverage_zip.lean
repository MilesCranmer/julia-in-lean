import JuliaLean.base.iterators
import JuliaLean.Proofs.base.iterators.coverage_enumerate

/-!
# `Iterators.Zip` (base/iterators.jl:376-526)

A `Zip` holds a tuple of component iterators `is`. Its state is the tuple of
component states; a component that has not been started yet is iterated with
`iterate(is[k])`, modelled by the position `none` (`ss[k] = ()` in Julia).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-! ## Specification -/

/-- The first `m` zipped tuples of the element lists `rs`. -/
def zipSpec : Nat → List (List V) → List V
  | 0, _ => []
  | m + 1, rs => .tup (rs.map (·.headD .nothing)) :: zipSpec m (rs.map List.tail)

/-- Component states that immediately yield the listed value-state pairs and
report \`missing\` from \`isdone\`. This is the branch where Julia's zip
implementation iterates every component in source order. -/
inductive Live : List (It × Option V) → List (V × V) → Prop
  | nil : Live [] []
  | cons {it : It} {o : Option V} {p : V × V}
      {cs : List (It × Option V)} {ps : List (V × V)} :
      doneOf it o = .ok none →
      stepOf it o = .ok (some p) →
      Live cs ps →
      Live ((it, o) :: cs) (p :: ps)

theorem zipIsdone_live {cs : List (It × Option V)} {ps : List (V × V)}
    (h : Live cs ps) :
    zipIsdone cs = .ok (false, List.replicate ps.length (none : Option Bool)) := by
  induction h with
  | nil => rfl
  | cons hd _ _ ih => simp [zipIsdone, hd, ih]; rfl

theorem zipInOrder_live {cs : List (It × Option V)} {ps : List (V × V)}
    (h : Live cs ps) : zipInOrder cs = .ok (some ps) := by
  induction h with
  | nil => rfl
  | cons _ hs _ ih => simp [zipInOrder, hs, ih]; rfl

theorem zipAllMissing_replicate (n : Nat) :
    zipAllMissing (List.replicate n (none : Option Bool)) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (none.isNone && zipAllMissing (List.replicate n (none : Option Bool))) = true
      rw [ih]
      rfl

/-- When every component yields immediately and reports \`missing\` from
\`isdone\`, \`_zip_iterate_all\` returns the tuple of yielded values and the
tuple of next states (base/iterators.jl:448-472). -/
theorem zipAll_live {cs : List (It × Option V)} {ps : List (V × V)}
    (h : Live cs ps) :
    zipAll cs = .ok (some (.tup (ps.map Prod.fst), .tup (ps.map Prod.snd))) := by
  simp only [zipAll, zipIsdone_live h]
  rw [zipAllMissing_replicate, zipInOrder_live h]
  rfl

/-- Every component answers \`false\` to \`isdone\`. -/
def ReadyFalse (cs : List (It × Option V)) : Prop :=
  ∀ c ∈ cs, doneOf c.1 c.2 = .ok (some false)

theorem zipAnyIsdone_false (cs : List (It × Option V)) (h : ReadyFalse cs) :
    zipAnyIsdone cs = .ok (some false) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hc := h c (List.mem_cons_self ..)
      have ht : ReadyFalse cs :=
        fun c' hc' => h c' (List.mem_cons_of_mem c hc')
      simp [zipAnyIsdone, hc, ih ht, or3]
      rfl

theorem zipAnyIsdone_true (pre : List (It × Option V)) (c : It × Option V)
    (post : List (It × Option V)) (hp : ReadyFalse pre)
    (hc : doneOf c.1 c.2 = .ok (some true)) :
    zipAnyIsdone (pre ++ c :: post) = .ok (some true) := by
  induction pre with
  | nil => simp [zipAnyIsdone, hc]; rfl
  | cons a pre ih =>
      have ha := hp a (List.mem_cons_self ..)
      have ht : ReadyFalse pre :=
        fun c' hc' => hp c' (List.mem_cons_of_mem a hc')
      simp [zipAnyIsdone, ha, ih ht, or3]
      rfl

/-- The zip iteration and \`isdone\` methods agree with their source bodies:
live components are stepped in order, all-false answers remain false, and the
first true answer stops the \`isdone\` scan (base/iterators.jl:430-501). -/
def ZipProtocol : Prop :=
  (∀ (cs : List (It × Option V)) (ps : List (V × V)), Live cs ps →
    zipAll cs = .ok (some (.tup (ps.map Prod.fst), .tup (ps.map Prod.snd)))) ∧
  (∀ cs, ReadyFalse cs → zipAnyIsdone cs = .ok (some false)) ∧
  (∀ pre c post, ReadyFalse pre → doneOf c.1 c.2 = .ok (some true) →
    zipAnyIsdone (pre ++ c :: post) = .ok (some true))

theorem zipProtocol : ZipProtocol :=
  ⟨fun _ _ => zipAll_live, zipAnyIsdone_false, zipAnyIsdone_true⟩

/-! ## Metadata and helper equations -/

/-- The remaining Zip helpers expose the shortest finite length, equal finite
length test, promoted size/axes, tuple eltype, last value and wrapper fields
exactly as `base/iterators.jl:380-425,503-521` specify. -/
def ZipMetadata : Prop :=
  (∀ its, zipLength its = do
    match ← zipMinLength its with
    | none => jthrow (.argumentError "iterator is of undefined length")
    | some n => pure n) ∧
  (zipMinLength [] = .ok none) ∧
  (∀ i is, zipMinLength (i :: is) = do
    let n ← zipMinLength is
    if i.isz = .isInfinite then pure n else
    match n with
    | none => do pure (some (← i.len))
    | some n => do pure (some (jmin n (← i.len)))) ∧
  (zipLFE [] = .ok (true, none)) ∧
  (∀ i is, zipLFE (i :: is) =
    if i.isz = .isInfinite ∨ i.isz = .sizeUnknown then .ok (false, none) else do
    let m ← i.len
    let (b, n) ← zipLFE is
    pure (b && (match n with | none => true | some n => decide (n = m)), some m)) ∧
  (∀ its, zipSize its = do pts (← its.mapM (·.size))) ∧
  (∀ m n, pts2 [m] [n] = .ok [jmin m n]) ∧
  (∀ a, pts [a] = .ok a) ∧
  (∀ its, (zipIt its).isz = zipTypeIsz (its.map (·.isz)) ∧
    (zipIt its).iel = zipTypeIel (its.map (·.iel)) ∧
    (zipIt its).elt = tupleOrBottom (its.map (·.elt)) ∧
    (zipIt its).len = zipLength its ∧ (zipIt its).size = zipSize its ∧
    (zipIt its).lastv = zipLast its) ∧
  (∀ its, zipLast its = do
    let n ← zipLength its
    let xs ← its.mapM fun it => nthGen it n.val
    pure (.tup xs))

theorem zipMetadata : ZipMetadata := by
  refine ⟨fun _ => rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ => rfl⟩

end JuliaLean.IteratorsCov
