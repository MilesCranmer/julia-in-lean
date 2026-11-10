import JuliaLean.Proofs.Compiler.src.typelattice.Common
import JuliaLean.Compiler.src.typelimits

/-!
`Union{}` is the identity of `tmerge`, layer by layer (`Compiler/src/typelimits.jl:450-789`).
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- `Union{}` as a lattice element. -/
def bot : LElt := .ty .bottom

theorem isBottom_eq {x : LElt} (h : x.isBottom = true) : x = bot := by
  cases x with
  | ty t => cases t <;> simp_all [LElt.isBottom, bot]
  | _ => simp [LElt.isBottom] at h

theorem run_bind_ok {α β : Type} {m : CM α} {f : α → CM β} {s s' : Nat} {v : α}
    (h : m.run s = .ok (v, s')) : (m >>= f).run s = (f v).run s' := by
  rw [StateT.run_bind, h]; rfl

theorem fastPath_bot_left (n : Nat) (E : CEnv) (L : Lattice) (x : LElt) (s : Nat) :
    (tmergeFastPath n E L bot x).run s = .ok (some x, s) := rfl

theorem fastPath_bot_right (n : Nat) (E : CEnv) (L : Lattice) (x : LElt) (s : Nat) :
    (tmergeFastPath n E L x bot).run s = .ok (some x, s) := by
  by_cases hx : x.isBottom = true
  · have := isBottom_eq hx; subst this; rfl
  · have hb : x.isBottom = false := by simpa using hx
    have hbb : bot.isBottom = true := rfl
    simp only [tmergeFastPath, hb, hbb, Bool.false_eq_true, if_false, if_true]
    rfl

def TmergeBottomPartials : Prop :=
  ∀ p n E (x : LElt) s,
    (tmerge (n + 1) E (.partials p) bot x).run s = .ok (x, s) ∧
    (tmerge (n + 1) E (.partials p) x bot).run s = .ok (x, s)

theorem tmergeBottomPartials_proven : TmergeBottomPartials := by
  intro p n E x s
  constructor
  · simp only [tmerge]
    rw [run_bind_ok (fastPath_bot_left n E _ x s)]
    rfl
  · simp only [tmerge]
    rw [run_bind_ok (fastPath_bot_right n E _ x s)]
    rfl


def TmergeBottomConditionals : Prop :=
  ∀ p n E (x : LElt) s,
    (tmerge (n + 1) E (.conditionals p) bot x).run s =
      (if x.isConditional then .ok (x, s) else (tmerge n E p bot x).run s) ∧
    (tmerge (n + 1) E (.conditionals p) x bot).run s =
      (if x.isConditional then .ok (x, s) else (tmerge n E p x bot).run s)

theorem tmergeBottomConditionals_proven : TmergeBottomConditionals := by
  intro p n E x s
  constructor <;> cases x <;> rfl

def TmergeBottomInterConditionals : Prop :=
  ∀ p n E (x : LElt) s,
    (tmerge (n + 1) E (.interConditionals p) bot x).run s =
      (if x.isInterConditional then .ok (x, s) else (tmerge n E p bot x).run s) ∧
    (tmerge (n + 1) E (.interConditionals p) x bot).run s =
      (if x.isInterConditional then .ok (x, s) else (tmerge n E p x bot).run s)

theorem tmergeBottomInterConditionals_proven : TmergeBottomInterConditionals := by
  intro p n E x s
  constructor <;> cases x <;> rfl

def TmergeBottomMustAliases : Prop :=
  ∀ p n E (x : LElt) s,
    ((tmerge (n + 1) E (.mustAliases p) bot x).run s =
      (if x.isMustAlias then .ok (x, s) else (tmerge n E p bot x).run s) ∧
    (tmerge (n + 1) E (.mustAliases p) x bot).run s =
      (if x.isMustAlias then .ok (x, s) else (tmerge n E p x bot).run s)) ∧
    ((tmerge (n + 1) E (.interMustAliases p) bot x).run s =
      (if x.isInterMustAlias then .ok (x, s) else (tmerge n E p bot x).run s) ∧
    (tmerge (n + 1) E (.interMustAliases p) x bot).run s =
      (if x.isInterMustAlias then .ok (x, s) else (tmerge n E p x bot).run s))

theorem tmergeBottomMustAliases_proven : TmergeBottomMustAliases := by
  intro p n E x s
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> cases x <;> rfl

def TmergeBottomInference : Prop :=
  ∀ p n E (x : LElt) s,
    (tmerge (n + 1) E (.inference p) bot x).run s =
      (if x.isLimited then .ok (x, s) else (tmerge n E p bot x).run s) ∧
    (tmerge (n + 1) E (.inference p) x bot).run s =
      (if x.isLimited then .ok (x, s) else (tmerge n E p x bot).run s)

theorem tmergeBottomInference_proven : TmergeBottomInference := by
  intro p n E x s
  constructor <;> cases x <;> rfl


theorem jl_left (n : Nat) (E : CEnv) (t : Val) (s : Nat) (ht : t.isType = true) :
    (tmerge (n + 1) E .jlType bot (.ty t)).run s =
      ((isconcretetype E t).run s).map (fun p => (LElt.ty t, p.2)) := by
  have hb : Val.bottom.isType = true := rfl
  have h0 : isconcretetype E Val.bottom = pure false := rfl
  have h1 : isType Val.bottom = false := rfl
  simp only [tmerge, bot, ht, hb, h0, h1, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    if_false, pure_bind, Bool.false_and, Bool.false_or]
  rw [StateT.run_bind]
  cases hc : (isconcretetype E t).run s with
  | error e => rfl
  | ok p =>
    rfl

theorem jl_right (n : Nat) (E : CEnv) (t : Val) (s : Nat) (ht : t.isType = true) :
    (tmerge (n + 1) E .jlType (.ty t) bot).run s =
      ((isconcretetype E t).run s).map (fun p => (LElt.ty t, p.2)) := by
  have hb : Val.bottom.isType = true := rfl
  have h0 : isconcretetype E Val.bottom = pure false := rfl
  have h1 : isType Val.bottom = false := rfl
  simp only [tmerge, bot, ht, hb, h0, h1, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    if_false, Bool.and_false, Bool.false_or]
  rw [StateT.run_bind]
  cases hc : (isconcretetype E t).run s with
  | error e => rfl
  | ok p =>
    have hf := fastPath_bot_right n E .jlType (.ty t) p.2
    simp only [Except.map, bind, Except.bind]
    simp only [StateT.bind, pure, StateT.pure, Except.pure, Bool.false_eq_true, if_false]
    rw [show ∀ (f : Bool → CM LElt), (StateT.pure false).bind f = f false from fun _ => rfl]
    simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact run_bind_ok hf

/-- On `JLTypeLattice`, `tmerge(Union{}, T)` and `tmerge(T, Union{})` return `T` for every type
`T`, or fail exactly when `isconcretetype(T)` does (the method's first query). -/
def TmergeBottomJLType : Prop :=
  ∀ n E (t : Val) s, t.isType = true →
    (tmerge (n + 1) E .jlType bot (.ty t)).run s =
      ((isconcretetype E t).run s).map (fun p => (LElt.ty t, p.2)) ∧
    (tmerge (n + 1) E .jlType (.ty t) bot).run s =
      ((isconcretetype E t).run s).map (fun p => (LElt.ty t, p.2))

theorem tmergeBottomJLType_proven : TmergeBottomJLType :=
  fun n E t s ht => ⟨jl_left n E t s ht, jl_right n E t s ht⟩

/-- `Union{}` is the identity of `tmerge` on the three lattices a `NativeInterpreter` uses
(`typeinf_lattice`, `ipo_lattice`, `optimizer_lattice`, `Compiler/src/types.jl:649-651`): for
every lattice element `x`, `tmerge(𝕃, Union{}, x)` and `tmerge(𝕃, x, Union{})` return `x` itself,
with no fresh objects and no error, given four steps of fuel (one per layer above
`PartialsLattice`). -/
def TmergeBottomDefault : Prop :=
  ∀ L, (L = typeinfLattice ∨ L = ipoLattice ∨ L = optimizerLattice) →
    ∀ n E (x : LElt) s,
      (tmerge (n + 4) E L bot x).run s = .ok (x, s) ∧
      (tmerge (n + 4) E L x bot).run s = .ok (x, s)

theorem tmergeBottomDefault_proven : TmergeBottomDefault := by
  intro L hL n E x s
  have hP := tmergeBottomPartials_proven .consts n E x s
  have hP1 := tmergeBottomPartials_proven .consts (n + 1) E x s
  rcases hL with h | h | h <;> subst h
  · obtain ⟨i1, i2⟩ := tmergeBottomInference_proven baseInferenceLattice (n + 3) E x s
    obtain ⟨⟨m1, m2⟩, _⟩ := tmergeBottomMustAliases_proven (.conditionals simpleInferenceLattice) (n + 2) E x s
    obtain ⟨c1, c2⟩ := tmergeBottomConditionals_proven simpleInferenceLattice (n + 1) E x s
    simp only [typeinfLattice, baseInferenceLattice, simpleInferenceLattice] at *
    rw [i1, i2, m1, m2, c1, c2, hP.1, hP.2]
    constructor <;> split <;> (try rfl) <;> split <;> (try rfl) <;> split <;> rfl
  · obtain ⟨i1, i2⟩ := tmergeBottomInference_proven ipoResultLattice (n + 3) E x s
    obtain ⟨_, ⟨m1, m2⟩⟩ := tmergeBottomMustAliases_proven (.interConditionals simpleInferenceLattice) (n + 2) E x s
    obtain ⟨c1, c2⟩ := tmergeBottomInterConditionals_proven simpleInferenceLattice (n + 1) E x s
    simp only [ipoLattice, ipoResultLattice, simpleInferenceLattice] at *
    rw [i1, i2, m1, m2, c1, c2, hP.1, hP.2]
    constructor <;> split <;> (try rfl) <;> split <;> (try rfl) <;> split <;> rfl
  · simp only [optimizerLattice, simpleInferenceLattice]
    exact tmergeBottomPartials_proven .consts (n + 3) E x s

end JuliaLean.Proofs.Compiler.src.typelimits
