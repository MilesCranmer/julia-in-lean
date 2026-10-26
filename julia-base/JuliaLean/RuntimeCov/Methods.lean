import JuliaLean.RuntimeCov.TypePreds

/-!
`base/runtime_internals.jl:1701-2093`: method reflection.  `MethodList` and
`methods`, the `_methods_by_ftype` wrappers around `jl_matching_methods`,
generator and IR accessors, `may_invoke_generator`, `subst_trivial_bounds`,
`normalize_typevars`, `specialize_method`, the method-table walk `visit`, and
the `specializations` iterator.

Methods are identified by numbers; the runtime's method matching, IR
decompression, and specialization caches are parameters.
-/

namespace JuliaLean.RuntimeCov.Methods

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.TypePreds

def typemaxUInt : Nat := 2 ^ 64 - 1

/-! ## MethodList and `methods` -/

/-- `MethodList(ms, tn)`, lines 1715-1716. -/
structure MethodList where
  ms : List Nat
  tn : Sym
  deriving DecidableEq, Repr

/-- `size(m::MethodList)`, line 1712, and `getindex(m, i)`, line 1713. -/
def mlSize (m : MethodList) : List Nat := [m.ms.length]
def mlGetindex (m : MethodList) (i : Int) : Rt Nat :=
  if 1 ≤ i ∧ i ≤ m.ms.length then .ok (m.ms.getD (i - 1).toNat 0) else .error .boundsError

/-- `matches_to_methods(ms, tn, mod)`, lines 1723-1731: `modOf m` is
`parentmodule(m)`; `mods = none` is `mod === nothing`. -/
def matchesToMethods (modOf : Nat → Sym) (ms : List Nat) (tn : Sym) (mods : Option (List Sym)) :
    MethodList :=
  match mods with
  | none => ⟨ms, tn⟩
  | some mods => ⟨ms.filter (fun m => mods.contains (modOf m)), tn⟩

/-- The arguments of one `jl_matching_methods` call. -/
structure MatchQuery where
  t : Ty
  mt : Option Nat
  lim : Int
  ambig : Bool
  world : Nat
  minWorld : Nat
  maxWorld : Nat
  deriving Repr

/-- `_methods_by_ftype` with eight arguments (line 1802), four (line 1799), and
three (line 1796). `jl` answers a query with a vector of matches or `nothing`. -/
def methodsByFtype8 (jl : MatchQuery → Option (List Nat)) (t : Ty) (mt : Option Nat) (lim : Int)
    (world : Nat) (ambig : Bool) (mn mx : Nat) : Option (List Nat) :=
  jl ⟨t, mt, lim, ambig, world, mn, mx⟩
def methodsByFtype4 (jl : MatchQuery → Option (List Nat)) (t : Ty) (mt : Option Nat) (lim : Int)
    (world : Nat) : Option (List Nat) :=
  methodsByFtype8 jl t mt lim world false 0 typemaxUInt
def methodsByFtype3 (jl : MatchQuery → Option (List Nat)) (t : Ty) (lim : Int) (world : Nat) :
    Option (List Nat) :=
  methodsByFtype4 jl t none lim world

/-- `_methods(f, t, lim, world)`, lines 1791-1794: `sig` is `signature_type(f, t)`. -/
def methods_ (jl : MatchQuery → Option (List Nat)) (sig : Rt Ty) (lim : Int) (world : Nat) :
    Rt (Option (List Nat)) := do
  let tt ← sig
  pure (methodsByFtype3 jl tt lim world)

def reflectionError : RtErr := .errorException "code reflection cannot be used from generated functions"

/-- `methods(f, t, mod)`, lines 1751-1757: `tn` is `typeof(f).name`. -/
def methods (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sig : Rt Ty) (tn : Sym)
    (world : Nat) (mods : Option (List Sym)) : Rt MethodList :=
  if world = typemaxUInt then .error reflectionError
  else do
    let ms ← methods_ jl sig (-1) world
    match ms with
    | none => .error .typeError
    | some ms => pure (matchesToMethods modOf ms tn mods)

/-- `methods(f, t, mod::Module)`, line 1758. -/
def methodsMod (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sig : Rt Ty) (tn : Sym)
    (world : Nat) (mod : Sym) : Rt MethodList :=
  methods jl modOf sig tn world (some [mod])

/-- `methods(f, mod)`, lines 1770-1774: `sigAll` is `signature_type(f, Tuple{Vararg{Any}})`. -/
def methodsAll (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sigAll : Rt Ty) (tn : Sym)
    (world : Nat) (mods : Option (List Sym)) : Rt MethodList :=
  methods jl modOf sigAll tn world mods

/-- `methods_including_ambiguous(f, t)`, lines 1760-1768. -/
def methodsIncludingAmbiguous (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sig : Rt Ty)
    (tn : Sym) (world : Nat) : Rt MethodList := do
  let tt ← sig
  if world = typemaxUInt then .error reflectionError
  else
    match methodsByFtype8 jl tt none (-1) world true 0 typemaxUInt with
    | none => .error .typeError
    | some ms => pure (matchesToMethods modOf ms tn none)

/-- Runtime calls issued by method mutators and specializers. -/
inductive Call where
  | disable (m : Nat)
  | lookup (m : Nat) (atype : Ty)
  | getLinfo (m : Nat) (atype : Ty) (sparams : List Ty)
  deriving Repr

/-- `delete_method(m)`, lines 1701-1703. -/
def deleteMethod (m : Nat) : Call := .disable m

/-! ## Method fields, IR and generators -/

inductive Source where
  | str (s : String)
  | codeInfo (c : Nat)
  | other
  deriving DecidableEq, Repr

structure Method where
  id : Nat
  source : Option Source
  hasGenerator : Bool
  nospecialize : Nat
  nospecializeinfer : Bool
  nargs : Nat
  isva : Bool
  sig : Ty
  deriving Repr

/-- `hasgenerator(m::Method)`, `hasgenerator(mi)`, lines 1806-1807. -/
def hasgenerator (m : Method) : Bool := m.hasGenerator
def hasgeneratorMI (miDef : Method) : Bool := hasgenerator miDef

/-- `_uncompressed_ir(m::Method)`, lines 1809-1815: `uncompress` is `jl_uncompress_ir`. -/
def uncompressedIr_ (uncompress : Method → String → Nat) (m : Method) (s : Source) : Rt Nat :=
  match s with
  | .str str => .ok (uncompress m str)
  | .codeInfo c => .ok c
  | .other => .error .typeError

/-- `_uncompressed_ir(codeinst, s)`, lines 1817-1818. -/
def uncompressedIrCI (uncompress : Method → Nat → String → Nat) (defMethod : Method) (ci : Nat)
    (s : String) : Nat := uncompress defMethod ci s

/-- `uncompressed_ir(m)`, lines 2089-2091. -/
def uncompressedIr (uncompress : Method → String → Nat) (m : Method) : Rt Nat :=
  match m.source with
  | some s => uncompressedIr_ uncompress m s
  | none =>
    if m.hasGenerator then .error (.errorException "Method is @generated; try `code_lowered` instead.")
    else .error (.errorException "Code for this Method is not available.")

/-- `codeinst.def`: a `MethodInstance` or an `ABIOverride` wrapping one. -/
inductive CIDef where
  | mi (m : Nat)
  | abiOverride (m : Nat)
  | other
  deriving DecidableEq, Repr

/-- `get_ci_mi(codeinst)`, lines 1820-1827. -/
def getCiMi (d : CIDef) : Rt Nat :=
  match d with
  | .abiOverride m => .ok m
  | .mi m => .ok m
  | .other => .error .typeError

/-- `generating_output(incremental)`, lines 1841-1847: `jlGen` is
`jl_generating_output()`, `optIncr` is `JLOptions().incremental != 0`. -/
def generatingOutput (jlGen : Int) (optIncr : Bool) (incremental : Option Bool) : Bool :=
  if jlGen = 0 then false
  else match incremental with
    | some inc => if optIncr == inc then true else false
    | none => true

/-- `ast_slotflag(code, i)`, line 1850: `jl_ir_slotflag(code, i - 1)`. -/
def astSlotflag {κ : Type} (rt : κ → Nat → Nat) (code : κ) (i : Nat) : Nat := rt code (i - 1)

/-- `has_image_globalref(m)`, line 2093. -/
def hasImageGlobalref (rt : Option Source → Bool) (m : Method) : Bool := rt m.source

def SLOT_USED : Nat := 0x8
def slotUsed (flag : Nat) : Bool := flag &&& SLOT_USED != 0

/-- The generator facts `may_invoke_generator` reads. -/
structure GenInfo where
  isStub : Bool
  genMethods : Option (List Nat)
  hasSource : Bool
  nslots : Nat
  slotflag : Nat → Nat

/-- The `for i = 1:non_va_args` loop of lines 1898-1904. -/
def checkArgs (slotflag : Nat → Nat) (nsp : Nat) (ps : List Ty) : List Nat → Rt Bool
  | [] => .ok true
  | i :: is =>
    match ps[i - 1]? with
    | none => .error .boundsError
    | some p =>
      if !isdispatchelem p && slotUsed (slotflag (1 + i + nsp)) then .ok false
      else checkArgs slotflag nsp ps is

/-- `may_invoke_generator(method, atype, sparams)`, lines 1870-1925: `isDT` is
`isdispatchtuple(atype)`, `atParams` the parameters of `unwrap_unionall(atype)`
when it is a `DataType`, `sparamIsSvec` the `isa(sparams[i], SimpleVector)`
tests. -/
def mayInvokeGenerator (isDT : Bool) (g : GenInfo) (m : Method) (atParams : Option (List Ty))
    (sparamIsSvec : List Bool) : Rt Bool :=
  if isDT then .ok true
  else if !g.isStub then .ok false
  else match g.genMethods with
    | none => .ok false
    | some gm =>
      if gm.length ≠ 1 then .ok false
      else if !g.hasSource then .ok false
      else match atParams with
        | none => .ok false
        | some ps =>
          let nsp := sparamIsSvec.length
          if !(decide (g.nslots ≥ 1 + nsp + ps.length)) then .ok false
          else if (List.range' 1 nsp).any (fun i => sparamIsSvec.getD (i - 1) false && slotUsed (g.slotflag (1 + i)))
          then .ok false
          else
            let nonva := if m.isva then m.nargs - 1 else m.nargs
            match checkArgs g.slotflag nsp ps (List.range' 1 nonva) with
            | .error e => .error e
            | .ok false => .ok false
            | .ok true =>
              if m.isva && slotUsed (g.slotflag (1 + m.nargs + nsp)) then
                .ok ((ps.drop nonva).all isdispatchelem)
              else .ok true

/-- `may_invoke_generator(mi)`, lines 1867-1869. -/
def mayInvokeGeneratorMI (isDT : Bool) (g : GenInfo) (miDef : Method) (atParams : Option (List Ty))
    (sparamIsSvec : List Bool) : Rt Bool :=
  mayInvokeGenerator isDT g miDef atParams sparamIsSvec

/-! ## Specialization -/

/-- `subst_trivial_bounds(atype)`, lines 1930-1947: `egal` is `===` on types,
`inst t ub` is `atype{v.ub}` (`none` when instantiation throws); recursion
depth is bounded by `fuel`. -/
def substTrivialBounds (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) : Nat → Ty → Ty
  | 0, t => t
  | f + 1, t =>
    match t with
    | .unionAll v lb ub body =>
      if isconcretetype ub || egal lb ub then
        match inst t ub with
        | some s => substTrivialBounds egal inst f s
        | none => .unionAll v lb ub (substTrivialBounds egal inst f body)
      else .unionAll v lb ub (substTrivialBounds egal inst f body)
    | _ => t

/-- The number of leading `UnionAll` binders. -/
def uaDepth : Ty → Nat
  | .unionAll _ _ _ b => uaDepth b + 1
  | _ => 0

/-- `normalize_typevars(method, atype, sparams)`, lines 1953-1960: `eqT` is `==`
on types, `env a b` the environment of `typeintersect_env(a, b)`. -/
def normalizeTypevars (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) (eqT : Ty → Ty → Bool)
    (env : Ty → Ty → List Ty) (m : Method) (atype : Ty) (sparams : List Ty) : Ty × List Ty :=
  let at2 := substTrivialBounds egal inst (uaDepth atype) atype
  if !egal at2 atype && eqT at2 atype then (at2, env at2 m.sig) else (atype, sparams)

/-- `get_nospecializeinfer_sig`, lines 1962-1966. -/
def getNospecializeinferSig (norm : Ty → List Ty → Method → Ty) (m : Method) (atype : Ty)
    (sparams : List Ty) : Ty :=
  match atype with
  | .dt _ _ => norm atype sparams m
  | _ => m.sig

/-- `is_nospecialized`, `is_nospecializeinfer`, lines 1968-1969. -/
def isNospecialized (m : Method) : Bool := m.nospecialize ≠ 0
def isNospecializeinfer (m : Method) : Bool := m.nospecializeinfer && isNospecialized m

/-- `specialize_method(method, atype, sparams; preexisting)`, lines 1979-1993. -/
def specializeMethod (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) (eqT : Ty → Ty → Bool)
    (env : Ty → Ty → List Ty) (norm : Ty → List Ty → Method → Ty) (m : Method) (atype : Ty)
    (sparams : List Ty) (preexisting : Bool := false) : Call :=
  let r := match atype with
    | .unionAll _ _ _ _ => normalizeTypevars egal inst eqT env m atype sparams
    | _ => (atype, sparams)
  let atype := if isNospecializeinfer m then getNospecializeinferSig norm m r.1 r.2 else r.1
  if preexisting then .lookup m.id atype else .getLinfo m.id atype r.2

/-- `specialize_method(match; kwargs...)`, lines 1995-1997. -/
structure MethodMatch where
  method : Method
  specTypes : Ty
  sparams : List Ty

def specializeMethodMatch (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) (eqT : Ty → Ty → Bool)
    (env : Ty → Ty → List Ty) (norm : Ty → List Ty → Method → Ty) (mm : MethodMatch)
    (preexisting : Bool := false) : Call :=
  specializeMethod egal inst eqT env norm mm.method mm.specTypes mm.sparams preexisting

/-! ## The method-table walk -/

/-- A `TypeMapEntry` chain (its `func` fields in `next` order) or a
`TypeMapLevel`, whose four `Memory{Any}` caches hold, in each value slot, a
nested `Memory{Any}` of maps or a map. -/
inductive TMap where
  | entry (funcs : List Nat)
  | level (targ arg1 tname name1 : Option (List (Option (Sum (List (Option TMap)) TMap))))
      (list any : Option TMap)

/-- The indices `3:2:n`. -/
def juliaSlots (n : Nat) : List Nat := List.range' 3 ((n - 1) / 2) 2

/-- `avisit(f, e)`, lines 2012-2027, given the visitor `v` for nested maps. -/
def avisit (v : TMap → List Nat) (e : List (Option (Sum (List (Option TMap)) TMap))) : List Nat :=
  (juliaSlots e.length).flatMap fun i =>
    match e[i - 1]? with
    | some (some (Sum.inl inner)) =>
      (juliaSlots inner.length).flatMap fun j =>
        match inner[j - 1]? with
        | some (some t) => v t
        | _ => []
    | some (some (Sum.inr t)) => v t
    | _ => []

/-- `visit(f, mc::TypeMapLevel)` (lines 2011-2043) and `visit(f, d::TypeMapEntry)`
(lines 2044-2050): the sequence of methods passed to `f`; `fuel` bounds the depth. -/
def visitTM : Nat → TMap → List Nat
  | 0, _ => []
  | _ + 1, .entry funcs => funcs
  | f + 1, .level targ arg1 tname name1 list any =>
    let a := fun (c : Option (List (Option (Sum (List (Option TMap)) TMap)))) =>
      match c with | some e => avisit (visitTM f) e | none => []
    a targ ++ a arg1 ++ a tname ++ a name1 ++
      (match list with | some l => visitTM f l | none => []) ++
      (match any with | some l => visitTM f l | none => [])

/-- A `Core.MethodTable` and its `defs`. -/
structure MethodTable where
  defs : Option TMap

/-- `visit(f, mt::Core.MethodTable)`, lines 2007-2010. -/
def visitMT (fuel : Nat) (mt : MethodTable) : List Nat :=
  match mt.defs with
  | some d => visitTM fuel d
  | none => []

/-- `MethodList(mt)`, lines 1715-1721; `length(mt)`, lines 2080-2086;
`isempty(mt)`, line 2087. -/
def methodListMT (fuel : Nat) (mt : MethodTable) : MethodList := ⟨visitMT fuel mt, "Any"⟩
def lengthMT (fuel : Nat) (mt : MethodTable) : Nat := (visitMT fuel mt).length
def isemptyMT (mt : MethodTable) : Bool := mt.defs.isNone

/-! ## Specializations -/

/-- `m.specializations`: unset/`nothing`, one `MethodInstance`, or a `SimpleVector`
with empty (`nothing`) slots. -/
inductive Specs where
  | none
  | one (mi : Nat)
  | svec (s : List (Option Nat))
  deriving DecidableEq, Repr

/-- `specializations(m)`, line 2059. -/
def specializations (defined : Bool) (s : Specs) : Specs := if defined then s else .none

inductive State where
  | nothing
  | idx (i : Nat)
  deriving DecidableEq, Repr

/-- The `while i < n && item === nothing` loop of lines 2071-2075, from index `i`. -/
def scan (s : List (Option Nat)) (i : Nat) : Option (Nat × Nat) :=
  if h : i < s.length then
    match s[i] with
    | some x => some (x, i + 1)
    | none => scan s (i + 1)
  else none
termination_by s.length - i

/-- `iterate(specs, i::Int)`, lines 2067-2077, on the `SimpleVector` `s`. -/
def iterateIdx (s : List (Option Nat)) (i : Nat) : Option (Nat × Nat) :=
  if i ≥ s.length then none else scan s i

/-- `iterate(specs)`, lines 2060-2065. -/
def iterateSpecs (sp : Specs) : Option (Nat × State) :=
  match sp with
  | .none => none
  | .one mi => some (mi, .nothing)
  | .svec s => (iterateIdx s 0).map fun r => (r.1, .idx r.2)

/-- `iterate(specs, ::Nothing)` (line 2066) and `iterate(specs, i::Int)`. -/
def iterateSpecsFrom (sp : Specs) (st : State) : Rt (Option (Nat × State)) :=
  match st, sp with
  | .nothing, _ => .ok none
  | .idx i, .svec s => .ok ((iterateIdx s i).map fun r => (r.1, .idx r.2))
  | .idx _, _ => .error .typeError

theorem scan_spec (s : List (Option Nat)) (i : Nat) :
    (scan s i = none ∧ (s.drop i).filterMap id = []) ∨
    (∃ x j, scan s i = some (x, j) ∧ i < j ∧ j ≤ s.length ∧
      (s.drop i).filterMap id = x :: (s.drop j).filterMap id) := by
  unfold scan
  split
  · rename_i h
    have hd : s.drop i = s[i] :: s.drop (i + 1) := List.drop_eq_getElem_cons h
    split
    · rename_i x hx
      right; refine ⟨x, i + 1, rfl, by omega, by omega, ?_⟩
      rw [hd, hx]; simp
    · rename_i hx
      rcases scan_spec s (i + 1) with ⟨h1, h2⟩ | ⟨x, j, h1, h2, h3, h4⟩
      · left; refine ⟨h1, ?_⟩; rw [hd, hx]; simpa using h2
      · right; refine ⟨x, j, h1, by omega, h3, ?_⟩; rw [hd, hx]; simpa using h4
  · rename_i h
    left; refine ⟨rfl, ?_⟩
    simp [List.drop_eq_nil_of_le (by omega : s.length ≤ i)]
termination_by s.length - i

theorem iterateIdx_spec (s : List (Option Nat)) (i : Nat) :
    (iterateIdx s i = none ∧ (s.drop i).filterMap id = []) ∨
    (∃ x j, iterateIdx s i = some (x, j) ∧ i < j ∧ j ≤ s.length ∧
      (s.drop i).filterMap id = x :: (s.drop j).filterMap id) := by
  unfold iterateIdx
  split
  · rename_i h; left; refine ⟨rfl, ?_⟩; simp [List.drop_eq_nil_of_le (by omega : s.length ≤ i)]
  · exact scan_spec s i

/-- The elements the iteration protocol produces from state `i`
(`count(Returns(true), specs)` counts them). -/
def enumFrom (s : List (Option Nat)) (i : Nat) : List Nat :=
  match h : iterateIdx s i with
  | none => []
  | some (x, j) => x :: enumFrom s j
termination_by s.length - i
decreasing_by
  rcases iterateIdx_spec s i with ⟨h1, _⟩ | ⟨x', j', h1, h2, h3, _⟩
  · rw [h1] at h; cases h
  · rw [h1] at h; cases h; omega

theorem enumFrom_eq (s : List (Option Nat)) (i : Nat) : enumFrom s i = (s.drop i).filterMap id := by
  rcases iterateIdx_spec s i with ⟨h1, h2⟩ | ⟨x, j, h1, h2, h3, h4⟩
  · rw [enumFrom, h2]; split
    · rfl
    · rename_i x j h; rw [h1] at h; cases h
  · rw [enumFrom, h4]; split
    · rename_i h; rw [h1] at h; cases h
    · rename_i x' j' h
      rw [h1] at h; cases h
      rw [enumFrom_eq s j]
termination_by s.length - i

/-- `length(specs::MethodSpecializations)`, line 2078. -/
def lengthSpecs (sp : Specs) : Nat :=
  match sp with
  | .none => 0
  | .one _ => 1
  | .svec s => (enumFrom s 0).length

/-! ## Properties -/

theorem juliaSlots_mem (n i : Nat) : i ∈ juliaSlots n ↔ 3 ≤ i ∧ i ≤ n ∧ i % 2 = 1 := by
  simp only [juliaSlots, List.mem_range']
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨(i - 3) / 2, by omega, by omega⟩

theorem checkArgs_sound (sf : Nat → Nat) (nsp : Nat) (ps : List Ty) :
    ∀ is, checkArgs sf nsp ps is = .ok true →
      ∀ i ∈ is, ∀ p, ps[i - 1]? = some p → slotUsed (sf (1 + i + nsp)) = true → isdispatchelem p = true
  | [], _, i, hi, _, _, _ => by simp at hi
  | k :: ks, h, i, hi, p, hp, hu => by
    simp only [checkArgs] at h
    split at h
    · cases h
    · rename_i q hq
      split at h
      · cases h
      · rename_i hc
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [hp] at hq; cases hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hc
          by_cases hd : isdispatchelem p = true
          · exact hd
          · exact absurd hu (by simp_all)
        · exact checkArgs_sound sf nsp ps ks h i hi p hp hu

theorem checkArgs_unused (sf : Nat → Nat) (nsp : Nat) (ps : List Ty) :
    ∀ is, (∀ i ∈ is, i - 1 < ps.length ∧ slotUsed (sf (1 + i + nsp)) = false) →
      checkArgs sf nsp ps is = .ok true
  | [], _ => rfl
  | k :: ks, h => by
    obtain ⟨h1, h2⟩ := h k (by simp)
    simp only [checkArgs, List.getElem?_eq_getElem h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact checkArgs_unused sf nsp ps ks (fun i hi => h i (by simp [hi]))

theorem substTrivialBounds_noinst (egal : Ty → Ty → Bool) (fuel : Nat) :
    ∀ t, substTrivialBounds egal (fun _ _ => none) fuel t = t := by
  induction fuel with
  | zero => intro t; rfl
  | succ f ih =>
    intro t
    cases t with
    | unionAll v lb ub body =>
      simp only [substTrivialBounds, ih]
      split <;> rfl
    | _ => rfl

def MethodsBodies : Prop :=
  (∀ m : MethodList, mlSize m = [m.ms.length]) ∧
  (∀ m : MethodList, ∀ i : Int, 1 ≤ i → i ≤ m.ms.length → mlGetindex m i = .ok (m.ms.getD (i - 1).toNat 0)) ∧
  (∀ m : MethodList, ∀ i : Int, (i < 1 ∨ m.ms.length < i) → mlGetindex m i = .error .boundsError) ∧
  -- `methods` with a module filter keeps exactly the matches defined in it, in
  -- the runtime's order
  (∀ jl modOf sig tn world mods r, methods jl modOf sig tn world (some mods) = .ok r →
      ∀ m ∈ r.ms, modOf m ∈ mods) ∧
  (∀ jl modOf sig tn world mods r, methods jl modOf sig tn world mods = .ok r →
      ∃ tt ms, sig = .ok tt ∧ jl ⟨tt, none, -1, false, world, 0, typemaxUInt⟩ = some ms ∧ r.ms.Sublist ms ∧
        r.tn = tn) ∧
  (∀ jl modOf sig tn mods, methods jl modOf sig tn typemaxUInt mods = .error reflectionError) ∧
  (∀ jl modOf sig tn world tt ms, world ≠ typemaxUInt → sig = .ok tt →
      jl ⟨tt, none, -1, false, world, 0, typemaxUInt⟩ = some ms →
      methods jl modOf sig tn world none = .ok ⟨ms, tn⟩) ∧
  (∀ jl modOf sig tn world mod, methodsMod jl modOf sig tn world mod = methods jl modOf sig tn world (some [mod])) ∧
  (∀ jl modOf sig tn world mods, methodsAll jl modOf sig tn world mods = methods jl modOf sig tn world mods) ∧
  (∀ jl modOf sig tn world tt ms, world ≠ typemaxUInt → sig = .ok tt →
      jl ⟨tt, none, -1, true, world, 0, typemaxUInt⟩ = some ms →
      methodsIncludingAmbiguous jl modOf sig tn world = .ok ⟨ms, tn⟩) ∧
  (∀ jl t lim world, methodsByFtype3 jl t lim world = jl ⟨t, none, lim, false, world, 0, typemaxUInt⟩) ∧
  (∀ jl t mt lim world, methodsByFtype4 jl t mt lim world = jl ⟨t, mt, lim, false, world, 0, typemaxUInt⟩) ∧
  (∀ jl tt lim world, methods_ jl (.ok tt) lim world = .ok (methodsByFtype3 jl tt lim world)) ∧
  (∀ m, deleteMethod m = .disable m) ∧
  (∀ m, hasgeneratorMI m = m.hasGenerator) ∧
  -- IR access: compressed sources are decompressed, generated-only methods and
  -- missing code are errors with their documented messages
  (∀ u m s, m.source = some (.str s) → uncompressedIr u m = .ok (u m s)) ∧
  (∀ u m c, m.source = some (.codeInfo c) → uncompressedIr u m = .ok c) ∧
  (∀ u m, m.source = none → m.hasGenerator = true →
      uncompressedIr u m = .error (.errorException "Method is @generated; try `code_lowered` instead.")) ∧
  (∀ u m, m.source = none → m.hasGenerator = false →
      uncompressedIr u m = .error (.errorException "Code for this Method is not available.")) ∧
  (∀ u d ci s, uncompressedIrCI u d ci s = u d ci s) ∧
  (∀ m, getCiMi (.abiOverride m) = .ok m ∧ getCiMi (.mi m) = .ok m) ∧
  -- `generating_output`: no output means false; `true`/`false` select package
  -- or system-image generation
  (∀ o i, generatingOutput 0 o i = false) ∧
  (∀ g o, g ≠ 0 → generatingOutput g o none = true) ∧
  (∀ g o inc, g ≠ 0 → (generatingOutput g o (some inc) = true ↔ o = inc)) ∧
  (∀ (κ : Type) (rt : κ → Nat → Nat) c i, astSlotflag rt c i = rt c (i - 1)) ∧
  (∀ rt m, hasImageGlobalref rt m = rt m.source) ∧
  -- `may_invoke_generator`
  (∀ g m atp sp, mayInvokeGenerator true g m atp sp = .ok true) ∧
  (∀ g m atp sp, g.isStub = false → mayInvokeGenerator false g m atp sp = .ok false) ∧
  (∀ g m sp, mayInvokeGenerator false g m none sp = .ok false ∨ ∃ e, mayInvokeGenerator false g m none sp = .error e) ∧
  (∀ g m ps sp, mayInvokeGenerator false g m (some ps) sp = .ok true →
      let nsp := sp.length
      let nonva := if m.isva then m.nargs - 1 else m.nargs
      (∀ i, 1 ≤ i → i ≤ nsp → sp.getD (i - 1) false = true → slotUsed (g.slotflag (1 + i)) = false) ∧
      (∀ i, 1 ≤ i → i ≤ nonva → ∀ p, ps[i - 1]? = some p → slotUsed (g.slotflag (1 + i + nsp)) = true →
        isdispatchelem p = true)) ∧
  (∀ g m ps sp, g.isStub = true → g.genMethods.map List.length = some 1 → g.hasSource = true →
      g.nslots ≥ 1 + sp.length + ps.length → m.isva = false → m.nargs ≤ ps.length →
      (∀ k, slotUsed (g.slotflag k) = false) → mayInvokeGenerator false g m (some ps) sp = .ok true) ∧
  (∀ isDT g m atp sp, mayInvokeGeneratorMI isDT g m atp sp = mayInvokeGenerator isDT g m atp sp) ∧
  -- trivial-bound substitution changes nothing when no bound can be substituted
  (∀ egal fuel t, substTrivialBounds egal (fun _ _ => none) fuel t = t) ∧
  (∀ egal inst fuel t, (∀ v lb ub b, t ≠ .unionAll v lb ub b) → substTrivialBounds egal inst fuel t = t) ∧
  (∀ egal eqT env m atype sp, (∀ t, egal t t = true) →
      normalizeTypevars egal (fun _ _ => none) eqT env m atype sp = (atype, sp)) ∧
  (∀ norm m d ps sp, getNospecializeinferSig norm m (.dt d ps) sp = norm (.dt d ps) sp m) ∧
  (∀ norm m t sp, (∀ d ps, t ≠ .dt d ps) → getNospecializeinferSig norm m t sp = m.sig) ∧
  (∀ m, isNospecializeinfer m = true → isNospecialized m = true) ∧
  -- `specialize_method` hands a concrete signature through unchanged
  (∀ egal inst eqT env norm m d ps sp, isNospecializeinfer m = false →
      specializeMethod egal inst eqT env norm m (.dt d ps) sp false = .getLinfo m.id (.dt d ps) sp ∧
      specializeMethod egal inst eqT env norm m (.dt d ps) sp true = .lookup m.id (.dt d ps)) ∧
  (∀ egal inst eqT env norm mm p, specializeMethodMatch egal inst eqT env norm mm p =
      specializeMethod egal inst eqT env norm mm.method mm.specTypes mm.sparams p) ∧
  -- the method-table walk reads only the value slots `3:2:length(e)`, all in bounds
  (∀ n i, i ∈ juliaSlots n ↔ 3 ≤ i ∧ i ≤ n ∧ i % 2 = 1) ∧
  (∀ f funcs, visitTM (f + 1) (.entry funcs) = funcs) ∧
  (∀ fuel mt, lengthMT fuel mt = (methodListMT fuel mt).ms.length) ∧
  (∀ fuel mt, isemptyMT mt = true → lengthMT fuel mt = 0) ∧
  -- the specializations iterator yields exactly the non-empty slots, in order
  (∀ s, specializations false s = .none ∧ specializations true s = s) ∧
  iterateSpecs .none = none ∧ (∀ mi, iterateSpecs (.one mi) = some (mi, .nothing)) ∧
  (∀ sp, iterateSpecsFrom sp .nothing = .ok none) ∧
  (∀ s i, enumFrom s i = (s.drop i).filterMap id) ∧
  (∀ s, lengthSpecs (.svec s) = (s.filterMap id).length) ∧
  (∀ s i, (iterateIdx s i = none ∧ (s.drop i).filterMap id = []) ∨
    (∃ x j, iterateIdx s i = some (x, j) ∧ i < j ∧ j ≤ s.length ∧
      (s.drop i).filterMap id = x :: (s.drop j).filterMap id))

theorem methodsBodies_proven : MethodsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; rfl
  · intro m i h1 h2; simp [mlGetindex, h1, h2]
  · intro m i h
    have : ¬ (1 ≤ i ∧ i ≤ (m.ms.length : Int)) := by omega
    simp [mlGetindex, this]
  · intro jl modOf sig tn world mods r h m hm
    unfold methods at h
    split at h
    · cases h
    · simp only [methods_, bind, Except.bind] at h
      cases hs : sig with
      | error e => rw [hs] at h; cases h
      | ok tt =>
        rw [hs] at h
        simp only [pure, Except.pure] at h
        split at h
        · cases h
        · rename_i ms _
          cases h
          simp only [matchesToMethods, List.mem_filter, List.contains_iff_mem] at hm
          exact hm.2
  · intro jl modOf sig tn world mods r h
    unfold methods at h
    split at h
    · cases h
    · simp only [methods_, bind, Except.bind] at h
      cases hs : sig with
      | error e => rw [hs] at h; cases h
      | ok tt =>
        rw [hs] at h
        simp only [pure, Except.pure] at h
        split at h
        · cases h
        · rename_i ms hms
          cases h
          refine ⟨tt, ms, rfl, ?_, ?_, ?_⟩
          · simpa [methodsByFtype3, methodsByFtype4, methodsByFtype8] using hms
          · cases mods with
            | none => exact List.Sublist.refl _
            | some ms' => exact List.filter_sublist
          · cases mods <;> rfl
  · intro _ _ _ _ _; simp [methods]
  · intro jl modOf sig tn world tt ms hw hs hj
    simp [methods, hw, methods_, hs, bind, Except.bind, methodsByFtype3, methodsByFtype4, methodsByFtype8,
      hj, pure, Except.pure, matchesToMethods]
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro jl modOf sig tn world tt ms hw hs hj
    simp [methodsIncludingAmbiguous, hw, hs, bind, Except.bind, methodsByFtype8, hj, pure, Except.pure,
      matchesToMethods]
  · intro _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl
  · intro _; rfl
  · intro u m s h; simp [uncompressedIr, h, uncompressedIr_]
  · intro u m c h; simp [uncompressedIr, h, uncompressedIr_]
  · intro u m h1 h2; simp [uncompressedIr, h1, h2]
  · intro u m h1 h2; simp [uncompressedIr, h1, h2]
  · intro _ _ _ _; rfl
  · intro _; exact ⟨rfl, rfl⟩
  · intro o i; simp [generatingOutput]
  · intro g o h; simp [generatingOutput, h]
  · intro g o inc h
    simp only [generatingOutput, h, ↓reduceIte]
    by_cases hc : o = inc <;> simp [hc]
  · intro _ _ _ _; rfl
  · intro _ _; rfl
  · intro _ _ _ _; rfl
  · intro g m atp sp h; simp [mayInvokeGenerator, h]
  · intro g m sp
    unfold mayInvokeGenerator
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · left; rfl
    · split
      · left; rfl
      · split
        · left; rfl
        · split
          · left; rfl
          · left; rfl
  · intro g m ps sp h
    simp only
    unfold mayInvokeGenerator at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    split at h
    · cases h
    · rename_i gm _
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      · rename_i hany
        split at h
        · cases h
        · cases h
        · rename_i hc
          refine ⟨?_, ?_⟩
          · intro i h1 h2 hs
            cases hu : slotUsed (g.slotflag (1 + i))
            · rfl
            · exfalso; apply hany
              simp only [List.any_eq_true, List.mem_range', Bool.and_eq_true]
              exact ⟨i, ⟨i - 1, by omega, by omega⟩, hs, hu⟩
          · intro i h1 h2 p hp hu
            apply checkArgs_sound _ _ _ _ hc i _ p hp hu
            apply List.mem_range'.mpr
            refine ⟨i - 1, ?_, by omega⟩
            revert h2; split <;> intro h2 <;> omega
  · intro g m ps sp hst hgm hsrc hsl hva hn hu
    cases hg : g.genMethods with
    | none => rw [hg] at hgm; cases hgm
    | some gm =>
      rw [hg] at hgm
      simp only [Option.map_some, Option.some.injEq] at hgm
      have hca : checkArgs g.slotflag sp.length ps (List.range' 1 m.nargs) = .ok true := by
        apply checkArgs_unused
        intro i hi
        simp only [List.mem_range'] at hi
        obtain ⟨k, hk, rfl⟩ := hi
        exact ⟨by omega, hu _⟩
      simp [mayInvokeGenerator, hst, hg, hgm, hsrc, hsl, hva, hu, hca]
  · intro _ _ _ _ _; rfl
  · exact fun egal fuel t => substTrivialBounds_noinst egal fuel t
  · intro egal inst fuel t ht
    cases fuel with
    | zero => rfl
    | succ f =>
      cases t with
      | unionAll v lb ub b => exact absurd rfl (ht v lb ub b)
      | _ => rfl
  · intro egal eqT env m atype sp hrefl
    simp [normalizeTypevars, substTrivialBounds_noinst, hrefl]
  · intro _ _ _ _ _; rfl
  · intro norm m t sp ht
    cases t with
    | dt d ps => exact absurd rfl (ht d ps)
    | _ => rfl
  · intro m h; simp only [isNospecializeinfer, Bool.and_eq_true] at h; exact h.2
  · intro egal inst eqT env norm m d ps sp h
    simp [specializeMethod, h]
  · intro _ _ _ _ _ _ _; rfl
  · exact juliaSlots_mem
  · intro _ _; rfl
  · intro _ _; rfl
  · intro fuel mt h
    simp only [isemptyMT, Option.isNone_iff_eq_none] at h
    simp [lengthMT, visitMT, h]
  · intro s; exact ⟨rfl, rfl⟩
  · rfl
  · intro _; rfl
  · intro sp; cases sp <;> rfl
  · exact enumFrom_eq
  · intro s; simp [lengthSpecs, enumFrom_eq]
  · exact iterateIdx_spec

end JuliaLean.RuntimeCov.Methods
