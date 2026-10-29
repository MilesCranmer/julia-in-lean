import JuliaLean.MiscCov.Basic

/-!
# `base/cmem.jl`, `base/osutils.jl`, `base/flfrontend.jl`, `base/coreir.jl`,
# `base/opaque_closure.jl` (master `bbfa0ce4150`)
-/

namespace JuliaLean.MiscCov

/-! ## `base/cmem.jl` -/

namespace CMem

/-- Process memory: the byte at each address. -/
abbrev Mem := Nat → Nat

/-- `ccall`'s conversion of an `Integer` argument to `Csize_t` (`convert(UInt64, n)`):
`InexactError` outside `0:typemax(UInt64)`. -/
def toCsize (n : Int) : M Nat :=
  if 0 ≤ n ∧ n < 2 ^ 64 then .ok n.toNat else .error .inexactError

/-- `n % Csize_t`: two's-complement reduction modulo `2^64`. -/
def remCsize (n : Int) : Nat := (n % 2 ^ 64).toNat

/-- `ccall`'s conversion of `val` to `Cint` (`convert(Int32, val)`). -/
def toCint (v : Int) : M Int :=
  if -(2 ^ 31) ≤ v ∧ v < 2 ^ 31 then .ok v else .error .inexactError

/-- C `memcpy(dst, src, n)` on non-overlapping ranges: returns `dst`. -/
def cMemcpy (m : Mem) (dst src n : Nat) : Mem × Nat :=
  (fun a => if dst ≤ a ∧ a < dst + n then m (src + (a - dst)) else m a, dst)

/-- C `memmove(dst, src, n)`: as if through a temporary buffer. -/
def cMemmove (m : Mem) (dst src n : Nat) : Mem × Nat :=
  (fun a => if dst ≤ a ∧ a < dst + n then m (src + (a - dst)) else m a, dst)

/-- C `memset(p, c, n)`: stores `(unsigned char)c`. -/
def cMemset (m : Mem) (p : Nat) (c : Int) (n : Nat) : Mem × Nat :=
  (fun a => if p ≤ a ∧ a < p + n then (c % 256).toNat else m a, p)

/-- C `memcmp(a, b, n)`: the sign of the first differing byte pair, `0` if none.
(glibc returns the byte difference; only its sign is specified.) -/
def cMemcmp (m : Mem) : Nat → Nat → Nat → Int
  | _, _, 0 => 0
  | a, b, n + 1 => if m a = m b then cMemcmp m (a + 1) (b + 1) n
    else if m a < m b then -1 else 1

/-- `memcpy(dst::Ptr, src::Ptr, n::Integer)`, `base/cmem.jl:12-15`. -/
def memcpy (m : Mem) (dst src : Nat) (n : Int) : M (Mem × Nat) := do
  let k ← toCsize n
  pure (cMemcpy m dst src k)

/-- `memmove(dst::Ptr, src::Ptr, n::Integer)`, `base/cmem.jl:26-29`. -/
def memmove (m : Mem) (dst src : Nat) (n : Int) : M (Mem × Nat) := do
  let k ← toCsize n
  pure (cMemmove m dst src k)

/-- `memset(p::Ptr, val, n::Integer)`, `base/cmem.jl:40-43`. -/
def memset (m : Mem) (p : Nat) (val : Int) (n : Int) : M (Mem × Nat) := do
  let c ← toCint val
  let k ← toCsize n
  pure (cMemset m p c k)

/-- `memcmp(a::Ptr, b::Ptr, n::Integer)`, `base/cmem.jl:54-57`: the length is `n % Csize_t`
and the `Cint` result is widened with `% Int`. -/
def memcmp (m : Mem) (a b : Nat) (n : Int) : M Int := .ok (cMemcmp m a b (remCsize n))

/-- The four wrappers call the C functions: for `0 ≤ n < 2^64`, `memcpy`/`memmove` make
`dst[k] == src[k]` for `k < n` and change nothing else, `memset` stores `val % 256`, all
return the destination pointer, and `memcmp` returns the sign of the first difference. -/
def Contract : Prop :=
  ∀ (m : Mem) (dst src : Nat) (n : Int), 0 ≤ n → n < 2 ^ 64 →
    (∃ m', memcpy m dst src n = .ok (m', dst) ∧
      (∀ k : Nat, k < n.toNat → m' (dst + k) = m (src + k)) ∧
      (∀ a, (a < dst ∨ dst + n.toNat ≤ a) → m' a = m a)) ∧
    (∃ m', memmove m dst src n = .ok (m', dst) ∧
      (∀ k : Nat, k < n.toNat → m' (dst + k) = m (src + k)) ∧
      (∀ a, (a < dst ∨ dst + n.toNat ≤ a) → m' a = m a)) ∧
    (∀ val : Int, -(2 ^ 31) ≤ val → val < 2 ^ 31 →
      ∃ m', memset m dst val n = .ok (m', dst) ∧
        ∀ k : Nat, k < n.toNat → m' (dst + k) = (val % 256).toNat) ∧
    memcmp m dst src n = .ok (cMemcmp m dst src n.toNat)

/-- A negative length is rejected with `InexactError` by every wrapper. -/
def NegativeLengthConsistent : Prop :=
  ∀ (m : Mem) (a b : Nat) (n : Int), n < 0 →
    memcpy m a b n = .error .inexactError ∧ memmove m a b n = .error .inexactError ∧
    memset m a 0 n = .error .inexactError ∧ memcmp m a b n = .error .inexactError

theorem contract_proven : Contract := by
  intro m dst src n h0 h1
  have hc : toCsize n = .ok n.toNat := by simp only [toCsize]; rw [if_pos ⟨h0, h1⟩]
  refine ⟨⟨(cMemcpy m dst src n.toNat).1, by simp only [memcpy, hc, bind, Except.bind, pure, Except.pure]; rfl, ?_, ?_⟩,
    ⟨(cMemmove m dst src n.toNat).1, by simp only [memmove, hc, bind, Except.bind, pure, Except.pure]; rfl, ?_, ?_⟩, ?_, ?_⟩
  · intro k hk; simp only [cMemcpy]; rw [if_pos (by omega)]; congr 1; omega
  · intro a ha; simp only [cMemcpy]; rw [if_neg (by omega)]
  · intro k hk; simp only [cMemmove]; rw [if_pos (by omega)]; congr 1; omega
  · intro a ha; simp only [cMemmove]; rw [if_neg (by omega)]
  · intro val hv0 hv1
    have hv : toCint val = .ok val := by simp only [toCint]; rw [if_pos ⟨hv0, hv1⟩]
    refine ⟨(cMemset m dst val n.toNat).1, by simp only [memset, hv, hc, bind, Except.bind, pure, Except.pure]; rfl, ?_⟩
    intro k hk; simp only [cMemset]; rw [if_pos (by omega)]
  · simp only [memcmp, remCsize]
    rw [Int.emod_eq_of_lt h0 h1]

theorem negativeLengthConsistent_refuted : ¬ NegativeLengthConsistent := by
  intro h
  have := (h (fun a => if a = 0 then 1 else 9) 0 1 (-1) (by decide)).2.2.2
  revert this
  decide

end CMem

/-! ## `base/osutils.jl` -/

namespace Static

/-- `@static ex`, `base/osutils.jl:24-48`. `evalCond` is `Core.eval(__module__, cond)`
followed by the `::Bool` assertion (a `TypeError` for a non-`Bool`); the `@goto loop`
over `elseif` branches is recursion on fuel (each step descends into an argument). -/
def static (evalCond : Ex → M Ex) : Nat → Ex → M Ex
  | 0, _ => .error (.other "fuel")
  | fuel + 1, ex =>
    match ex with
    | .expr hd args =>
      if hd ∈ ["if", "elseif", "&&", "||"] then
        match args with
        | c :: a2 :: rest => do
          let cv ← evalCond c
          match cv with
          | .bool cond =>
            if xor cond (hd == "||") then pure (Ex.esc a2)
            else match rest with
              | [br] =>
                match br with
                | .expr "elseif" _ => static evalCond fuel br
                | _ => pure (Ex.esc br)
              | _ =>
                if hd == "if" || hd == "elseif" then pure .nothing
                else pure (.bool cond)
          | _ => .error .typeError
        | _ => .error .boundsError
      else .error (.argumentError "invalid @static macro")
    | _ => .error (.argumentError "invalid @static macro")

/-- What a conditional evaluates to when its conditions are the given Booleans:
the selected branch (escaped), `nothing` for an `if` with no taken branch, the value
`cond` of a short-circuit whose right side is skipped. -/
def select (evalCond : Ex → M Ex) : Nat → Ex → M Ex := static evalCond

/-- `@static` selects exactly the branch the run-time conditional would take: for
`if c a [else b]`, `a` when `c` is true, else the `else`/`elseif` part (recursively) or
`nothing`; for `c && a`, `a` or `false`; for `c || a`, `true` or `a`; a non-`Bool`
condition is a `TypeError` and any other expression an `ArgumentError`. -/
def Contract : Prop :=
  ∀ (evalCond : Ex → M Ex) (fuel : Nat) (c a b : Ex),
    (evalCond c = .ok (.bool true) →
      static evalCond (fuel + 1) (.expr "if" [c, a]) = .ok (Ex.esc a) ∧
      static evalCond (fuel + 1) (.expr "if" [c, a, b]) = .ok (Ex.esc a) ∧
      static evalCond (fuel + 1) (.expr "&&" [c, a]) = .ok (Ex.esc a) ∧
      static evalCond (fuel + 1) (.expr "||" [c, a]) = .ok (.bool true)) ∧
    (evalCond c = .ok (.bool false) →
      static evalCond (fuel + 1) (.expr "if" [c, a]) = .ok .nothing ∧
      ((¬ b.isExpr "elseif") → static evalCond (fuel + 1) (.expr "if" [c, a, b]) = .ok (Ex.esc b)) ∧
      (∀ bargs, static evalCond (fuel + 1) (.expr "if" [c, a, .expr "elseif" bargs]) =
        static evalCond fuel (.expr "elseif" bargs)) ∧
      static evalCond (fuel + 1) (.expr "&&" [c, a]) = .ok (.bool false) ∧
      static evalCond (fuel + 1) (.expr "||" [c, a]) = .ok (Ex.esc a)) ∧
    (∀ v, evalCond c = .ok v → (∀ x, v ≠ .bool x) →
      static evalCond (fuel + 1) (.expr "if" [c, a]) = .error .typeError) ∧
    (∀ hd args, hd ∉ ["if", "elseif", "&&", "||"] →
      static evalCond (fuel + 1) (.expr hd args) = .error (.argumentError "invalid @static macro")) ∧
    (∀ x, (∀ hd args, x ≠ .expr hd args) →
      static evalCond (fuel + 1) x = .error (.argumentError "invalid @static macro"))

theorem contract_proven : Contract := by
  intro evalCond fuel c a b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [static, h, bind, Except.bind, pure, Except.pure]
  · intro h
    refine ⟨by simp [static, h, bind, Except.bind, pure, Except.pure], ?_, ?_,
      by simp [static, h, bind, Except.bind, pure, Except.pure],
      by simp [static, h, bind, Except.bind, pure, Except.pure]⟩
    · intro hb
      cases b with
      | expr hd args =>
        by_cases he : hd = "elseif"
        · subst he; simp [Ex.isExpr] at hb
        · simp [static, h, bind, Except.bind, pure, Except.pure, he]
      | _ => simp [static, h, bind, Except.bind, pure, Except.pure]
    · intro bargs; simp [static, h, bind, Except.bind, pure, Except.pure]
  · intro v h hv
    cases v <;> simp_all [static, bind, Except.bind]
  · intro hd args hn
    simp [static, hn]
  · intro x hx
    cases x <;> simp_all [static]

end Static

/-! ## `base/flfrontend.jl` -/

namespace FlFrontend

/-- The arguments `jl_fl_parse` receives. -/
structure ParseCall where
  text : List Nat
  len : Nat
  filename : String
  lineno : Int
  offset : Int
  deriving DecidableEq, Repr

/-- The text argument: a `String` (its bytes) or a `Core.SimpleVector` `(text, len)`
built by the C entry points. -/
inductive Text where
  | str (bytes : List Nat)
  | svec (bytes : List Nat) (len : Nat)

/-- `fl_parse(text::Union{Core.SimpleVector,String}, filename::String, lineno, offset,
options, edition)`, `base/flfrontend.jl:5-18`: the edition check, then the `ccall`;
`VERSION_EDITION` is `versionEdition`. The parser result is not modelled: the value
is the argument record of the call. -/
def flParse (versionEdition : String) (text : Text) (filename : String) (lineno offset : Int)
    (edition : String) : M ParseCall :=
  if edition ≠ versionEdition then .error (.errorException "Edition not supported by flisp parser")
  else
    let (t, len) := match text with
      | .svec t l => (t, l)
      | .str t => (t, t.length)
    .ok ⟨t, len, filename, lineno, offset⟩

/-- `fl_parse(text::AbstractString, filename::AbstractString, ...)`, `base/flfrontend.jl:20-23`:
convert both to `String` (the same bytes) and call the method above. -/
def flParseAbstract (versionEdition : String) (bytes : List Nat) (filename : String)
    (lineno offset : Int) (edition : String) : M ParseCall :=
  flParse versionEdition (.str bytes) filename lineno offset edition

/-- The arguments `jl_fl_lower` receives. -/
structure LowerCall where
  filename : String
  lineno : Int
  world : Nat
  warn : Bool
  deriving DecidableEq, Repr

/-- `fl_lower(ex, mod, filename="none", lineno=0, world=typemax(Csize_t), warn=false)`,
`base/flfrontend.jl:25-29`: the defaults, passed to `jl_fl_lower`. -/
def flLower (filename : String := "none") (lineno : Int := 0) (world : Nat := 2 ^ 64 - 1)
    (warn : Bool := false) : LowerCall := ⟨filename, lineno, world, warn⟩

/-- `fl_parse` rejects another edition with `ErrorException`; otherwise it passes the
byte length `sizeof(text)` of a `String` (and the given length of a `SimpleVector`);
the `AbstractString` method is the `String` method on the converted text; `fl_lower`
passes its arguments, with defaults `"none"`, `0`, `typemax(Csize_t)`, `false`. -/
def Contract : Prop :=
  ∀ (ve e fname : String) (bytes : List Nat) (len : Nat) (lineno offset : Int),
    (e ≠ ve → ∀ text, flParse ve text fname lineno offset e =
      .error (.errorException "Edition not supported by flisp parser")) ∧
    (e = ve → flParse ve (.str bytes) fname lineno offset e = .ok ⟨bytes, bytes.length, fname, lineno, offset⟩ ∧
      flParse ve (.svec bytes len) fname lineno offset e = .ok ⟨bytes, len, fname, lineno, offset⟩) ∧
    flParseAbstract ve bytes fname lineno offset e = flParse ve (.str bytes) fname lineno offset e ∧
    flLower = ⟨"none", 0, 2 ^ 64 - 1, false⟩ ∧
    (∀ w warn, flLower fname lineno w warn = ⟨fname, lineno, w, warn⟩)

theorem contract_proven : Contract := by
  intro ve e fname bytes len lineno offset
  refine ⟨?_, ?_, rfl, rfl, fun _ _ => rfl⟩
  · intro h text; simp [flParse, h]
  · intro h; subst h; simp [flParse]

end FlFrontend

/-! ## `base/coreir.jl` -/

namespace CoreIR

/-- A lattice element of `fields`: we only need whether it is `Union{}` and whether it
is a `Vararg`. -/
structure Lat where
  tag : Nat
  isBottom : Bool
  isVararg : Bool
  deriving DecidableEq, Repr

/-- What `PartialStruct` checks of `typ`: `fieldcount_noerror(typ)` (`none` for a
variable-length tuple), `typ <: Tuple`, and `datatype_min_ninitialized(typ)`. -/
structure TypInfo where
  id : Nat
  fldcnt : Option Nat
  isTuple : Bool
  minInit : Nat
  deriving DecidableEq, Repr

/-- `undefs` entries: `nothing`, `false`, `true`. -/
abbrev Undef := Option Bool

structure PartialStruct where
  typ : TypInfo
  undefs : List Undef
  fields : List Lat
  deriving DecidableEq, Repr

/-- `Core.PhiNode() = Core.PhiNode(Int32[], Any[])`, `base/coreir.jl:3`: the edges and
values of the node. -/
def phiNode : List Int × List Lat := ([], [])

/-- The conditions asserted by `Core.PartialStruct(typ::Type, undefs, fields)`,
`base/coreir.jl:50-64`, in order; `none` is a `BoundsError` from `fields[end]` on an
empty vector. -/
def mk3Checks (typ : TypInfo) (undefs : List Undef) (fields : List Lat) : Option Bool :=
  match typ.fldcnt with
  | some n => some ((n == fields.length) && fields.length == undefs.length && loopOk)
  | none =>
    match fields.getLast? with
    | none => none
    | some f => some (typ.isTuple && f.isVararg && typ.minInit == fields.length - 1 &&
        undefs.getLast? == some none && fields.length == undefs.length && loopOk)
where
  /-- `for i = 1:length(fields); fields[i] === Union{} && @assert undefs[i] === true; end` -/
  loopOk : Bool := (List.range fields.length).all fun i =>
    !(fields.getD i ⟨0, false, false⟩).isBottom || undefs.getD i none == some true

/-- `Core.PartialStruct(typ::Type, undefs, fields)`, `base/coreir.jl:50-66`: every failed
`@assert` throws `AssertionError`. -/
def mk3 (typ : TypInfo) (undefs : List Undef) (fields : List Lat) : M PartialStruct :=
  match mk3Checks typ undefs fields with
  | none => .error .boundsError
  | some true => .ok ⟨typ, undefs, fields⟩
  | some false => .error .assertionError

/-- `partialstruct_init_undefs(typ, fields)`, `base/coreir.jl:75-93`; `none` is the
returned `nothing`. Indices are 1-based in Julia. -/
def initUndefs (typ : TypInfo) (fields : List Lat) : Option (List Undef) :=
  let nf := fields.length
  let minf := typ.minInit
  if (fields.take minf).any (·.isBottom) then none
  else some ((List.range nf).map fun i =>
    if i < minf then some false
    else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none)

/-- `Core.PartialStruct(typ, fields::Vector{Any})`, `base/coreir.jl:69-73`. -/
def mk2 (typ : TypInfo) (fields : List Lat) : M PartialStruct :=
  match initUndefs typ fields with
  | none => .error (.errorException "This object never exists at runtime")
  | some undefs => mk3 typ undefs fields

/-- `a::PartialStruct == b::PartialStruct`, `base/coreir.jl:95`. -/
def eq (a b : PartialStruct) : Bool := a.typ == b.typ && a.undefs == b.undefs && a.fields == b.fields

/-- `getproperty(pstruct::PartialStruct, name)`, `base/coreir.jl:97-100`. -/
inductive Field | typ | undefs | fields
def getproperty (p : PartialStruct) : Field → (TypInfo ⊕ List Undef ⊕ List Lat)
  | .undefs => .inr (.inl p.undefs)
  | .typ => .inl p.typ
  | .fields => .inr (.inr p.fields)

/-- The two-argument constructor builds a `PartialStruct` satisfying every assertion of
the three-argument one (`base/coreir.jl:22-48` docstring): for a struct with `n` fields
and `n` lattice elements, and for a variable-length tuple whose last element is the
`Vararg` and whose `min_ninitialized` is `n - 1`, it errors exactly when one of the first
`min_ninitialized` fields is `Union{}`, and otherwise marks those fields `false`, a
later `Union{}` field `true`, the rest `nothing`; `==` compares the three fields and
`getproperty` returns them. -/
def Contract : Prop :=
  (phiNode = ([], [])) ∧
  (∀ (typ : TypInfo) (fields : List Lat),
    ((∃ n, typ.fldcnt = some n ∧ n = fields.length ∧ typ.minInit ≤ n) ∨
     (typ.fldcnt = none ∧ typ.isTuple ∧ (fields.getLast?.map (·.isVararg)) = some true ∧
       (fields.getLast?.map (·.isBottom)) = some false ∧ typ.minInit + 1 = fields.length)) →
    ((fields.take typ.minInit).any (·.isBottom) → mk2 typ fields =
        .error (.errorException "This object never exists at runtime")) ∧
    (¬ (fields.take typ.minInit).any (·.isBottom) → ∃ p, mk2 typ fields = .ok p ∧
      p.typ = typ ∧ p.fields = fields ∧ p.undefs.length = fields.length ∧
      ∀ i, i < fields.length →
        p.undefs.getD i none = (if i < typ.minInit then some false
          else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none))) ∧
  (∀ a b : PartialStruct, eq a b = true ↔ a = b) ∧
  (∀ p : PartialStruct, getproperty p .undefs = .inr (.inl p.undefs) ∧
    getproperty p .typ = .inl p.typ ∧ getproperty p .fields = .inr (.inr p.fields))

theorem initUndefs_getD (typ : TypInfo) (fields : List Lat) (i : Nat) (hi : i < fields.length) :
    ((List.range fields.length).map fun i =>
      if i < typ.minInit then some false
      else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else (none : Undef)).getD i none =
    (if i < typ.minInit then some false
      else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem contract_proven : Contract := by
  refine ⟨rfl, ?_, ?_, fun p => ⟨rfl, rfl, rfl⟩⟩
  · intro typ fields hpre
    refine ⟨?_, ?_⟩
    · intro hb
      simp [mk2, initUndefs, hb]
    · intro hb
      have hU : initUndefs typ fields = some ((List.range fields.length).map fun i =>
          if i < typ.minInit then some false
          else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none) := by
        simp [initUndefs, hb]
      obtain ⟨U, hUdef⟩ : ∃ U : List Undef, U = (List.range fields.length).map fun i =>
          if i < typ.minInit then some false
          else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else (none : Undef) :=
        ⟨_, rfl⟩
      rw [← hUdef] at hU
      have hlen : U.length = fields.length := by simp [hUdef]
      -- no field before `minInit` is `Union{}`
      have hnb : ∀ i, i < typ.minInit → i < fields.length →
          (fields.getD i ⟨0, false, false⟩).isBottom = false := by
        intro i h1 h2
        have : ¬ (fields.take typ.minInit).any (·.isBottom) = true := hb
        simp only [List.any_eq_true, not_exists, not_and] at this
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
        have hm : fields[i] ∈ fields.take typ.minInit :=
          List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
        simpa using this _ hm
      have hloop : ((List.range fields.length).all fun i =>
          !(fields.getD i ⟨0, false, false⟩).isBottom || U.getD i none == some true) = true := by
        rw [List.all_eq_true]
        intro i hi
        have hi' := List.mem_range.mp hi
        rw [hUdef, initUndefs_getD typ fields i hi']
        by_cases h1 : i < typ.minInit
        · rw [if_pos h1, hnb i h1 hi']; rfl
        · by_cases h2 : (fields.getD i ⟨0, false, false⟩).isBottom <;> simp [h1, h2]
      refine ⟨⟨typ, U, fields⟩, ?_, rfl, rfl, hlen, ?_⟩
      · simp only [mk2, hU, mk3]
        rcases hpre with ⟨n, hn, hnl, _⟩ | ⟨hn, ht, hv, hbot, hmin⟩
        · have hc : mk3Checks typ U fields = some true := by
            simp only [mk3Checks, mk3Checks.loopOk, hn, hloop, hnl, hlen, beq_self_eq_true, Bool.and_true]
          rw [hc]
        · have hidx : fields.length - 1 < fields.length := by omega
          have hnot : ¬ (fields.length - 1 < typ.minInit) := by omega
          obtain ⟨f, hf⟩ : ∃ f, fields.getLast? = some f := by
            cases h : fields.getLast? with
            | none => simp [h] at hv
            | some f => exact ⟨f, rfl⟩
          have hfv : f.isVararg = true := by simpa [hf] using hv
          have hfb : f.isBottom = false := by simpa [hf] using hbot
          have hget : fields.getD (fields.length - 1) ⟨0, false, false⟩ = f := by
            rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hf]; rfl
          have hlast : U.getLast? = some none := by
            rw [List.getLast?_eq_getElem?, hlen, hUdef, List.getElem?_map, List.getElem?_range hidx]
            simp only [Option.map]
            rw [if_neg hnot, hget, hfb]; rfl
          have hm' : typ.minInit = fields.length - 1 := by omega
          have hc : mk3Checks typ U fields = some true := by
            simp only [mk3Checks, mk3Checks.loopOk, hn, hf, ht, hfv, hlast, hloop, hlen, hm', Bool.true_and,
              beq_self_eq_true, Bool.and_true]
          rw [hc]
      · intro i hi
        rw [hUdef, initUndefs_getD typ fields i hi]
  · intro a b
    constructor
    · intro h
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      cases a; cases b; simp_all
    · intro h; subst h; simp [eq]

end CoreIR

/-! ## `base/opaque_closure.jl` -/

namespace OpaqueClosure

/-- `@opaque ex`, `base/opaque_closure.jl:20-22`. -/
def opaque1 (ex : Ex) : Ex :=
  Ex.esc (.expr "opaque_closure" [.nothing, .nothing, .nothing, .bool true, ex])

/-- `@opaque ty ex`, `base/opaque_closure.jl:24-38`: `ty` must be `AT -> RT` whose body,
without line numbers, is a block of one expression; `_` stands for `nothing`. -/
def opaque2 (ty ex : Ex) : M Ex :=
  match ty with
  | .expr "->" [AT, body] =>
    let bargs := (body.args?.getD []).filter (fun x => !x.isLnn)
    if !(body.isExpr "block") || bargs.length != 1 then
      .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")
    else
      let RT := bargs.head!
      let AT := if !AT.isSym "_" then AT else .nothing
      let RT := if !RT.isSym "_" then RT else .nothing
      .ok (Ex.esc (.expr "opaque_closure" [AT, RT, RT, .bool true, ex]))
  | _ => .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")

/-- The argument record of `jl_new_opaque_closure_from_code_info`. -/
structure NewOC where
  sig : String
  rtLb : String
  rtUb : String
  mod : String
  lineno : Int
  file : Option String
  nargs : Int
  isva : Bool
  env : List String
  doCompile : Bool
  isinferred : Bool
  deriving DecidableEq, Repr

/-- `generate_opaque_closure(sig, rt_lb, rt_ub, src, nargs, isva, env...; mod=@__MODULE__,
lineno=0, file=nothing, do_compile=true, isinferred=true)`, `base/opaque_closure.jl:47-56`;
`@__MODULE__` there is `Base`. -/
def generate (sig rtLb rtUb : String) (nargs : Int) (isva : Bool) (env : List String)
    (mod : String := "Base") (lineno : Int := 0) (file : Option String := none)
    (doCompile : Bool := true) (isinferred : Bool := true) : NewOC :=
  ⟨sig, rtLb, rtUb, mod, lineno, file, nargs, isva, env, doCompile, isinferred⟩

/-- `Core.OpaqueClosure(src, env...; rettype, sig, nargs, isva=false, kwargs...)`,
`base/opaque_closure.jl:43-45`. -/
def ofCodeInfo (env : List String) (rettype sig : String) (nargs : Int) (isva : Bool := false) : NewOC :=
  generate sig "Union{}" rettype nargs isva env

/-- The macros build the documented `:opaque_closure` expression (no types, or the
argument and return types of `AT -> RT`, with `_` meaning unspecified) and reject any
other type syntax; `Core.OpaqueClosure` asks for return type bounds `Union{}` to
`rettype` with the defaults of `generate_opaque_closure`. -/
def Contract : Prop :=
  (∀ ex, opaque1 ex = Ex.esc (.expr "opaque_closure" [.nothing, .nothing, .nothing, .bool true, ex])) ∧
  (∀ (AT RT ex : Ex), RT.isLnn = false →
    opaque2 (.expr "->" [AT, .expr "block" [.lnn, RT]]) ex =
      .ok (Ex.esc (.expr "opaque_closure"
        [if AT.isSym "_" then .nothing else AT, if RT.isSym "_" then .nothing else RT,
         if RT.isSym "_" then .nothing else RT, .bool true, ex]))) ∧
  (∀ ty ex, (∀ AT body, ty ≠ .expr "->" [AT, body]) →
    opaque2 ty ex = .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")) ∧
  (∀ (AT ex : Ex) (xs : List Ex), (xs.filter (fun x => !x.isLnn)).length ≠ 1 →
    opaque2 (.expr "->" [AT, .expr "block" xs]) ex =
      .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")) ∧
  (∀ env rettype sig nargs isva, ofCodeInfo env rettype sig nargs isva =
    ⟨sig, "Union{}", rettype, "Base", 0, none, nargs, isva, env, true, true⟩)

theorem contract_proven : Contract := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, fun _ _ _ _ _ => rfl⟩
  · intro AT RT ex hRT
    have hl : Ex.isLnn .lnn = true := rfl
    have hf : ([Ex.lnn, RT].filter (fun x => !x.isLnn)) = [RT] := by
      simp only [List.filter, hl, hRT, Bool.not_true, Bool.not_false]
    simp only [opaque2, Ex.args?, Option.getD_some, hf, Ex.isExpr]
    cases ha : AT.isSym "_" <;> cases hr : RT.isSym "_" <;> simp [ha, hr, List.head!]
  · intro ty ex h
    unfold opaque2
    split
    · rename_i AT body; exact absurd rfl (h AT body)
    · rfl
  · intro AT ex xs h
    simp [opaque2, Ex.args?, Ex.isExpr, h]

end OpaqueClosure

end JuliaLean.MiscCov
