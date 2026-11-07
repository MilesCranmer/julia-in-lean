import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.bool
import JuliaLean.base.float
import JuliaLean.base.operators

/-!
# Model of `base/promotion.jl`

Typed model of the methods in Julia's promotion machinery. Dynamic type operations,
conversion, inference, dispatch and value-level arithmetic are explicit function parameters.
-/

namespace JuliaLean.base.promotion

open JuliaLean

/-! ## Runtime type representation and operations -/

inductive PVarargLength where
  | open
  | int (n : Nat)
  | nonInt
  deriving BEq, DecidableEq, Repr, Inhabited

/-- `Core.TypeName` identity: the defining module and the name. -/
structure TypeName where
  module : String
  name : String
  deriving DecidableEq, Repr, Inhabited

def anyTypeName : TypeName := ⟨"Core", "Any"⟩
def tupleTypeName : TypeName := ⟨"Core", "Tuple"⟩

inductive PType where
  | bottom
  | any
  | typeVar (id : Nat) (upper : PType)
  | unionAll (var body : PType)
  | union (left right : PType)
  | data (name : TypeName) (wrapper : String) (params : List PType) (super : Option PType)
  | typeEq (parameter : PType)
  | typeEgal (parameter : PType)
  | vararg (element : PType) (length : PVarargLength)
  | parameter (tag : String)
  deriving Repr
instance : Inhabited PType := ⟨.bottom⟩

mutual
def pEqual : PType → PType → Bool
  | .bottom, .bottom | .any, .any => true
  | .typeVar i a, .typeVar j b => i == j && pEqual a b
  | .unionAll v a, .unionAll w b => pEqual v w && pEqual a b
  | .union a b, .union c d => pEqual a c && pEqual b d
  | .data n w ps sup, .data n' w' ps' sup' =>
      n == n' && w == w' && pListEqual ps ps' && pOptionEqual sup sup'
  | .typeEq a, .typeEq b | .typeEgal a, .typeEgal b => pEqual a b
  | .vararg a n, .vararg b m => pEqual a b && decide (n = m)
  | .parameter a, .parameter b => a == b
  | _, _ => false

def pListEqual : List PType → List PType → Bool
  | [], [] => true
  | a :: as, b :: bs => pEqual a b && pListEqual as bs
  | _, _ => false

def pOptionEqual : Option PType → Option PType → Bool
  | none, none => true
  | some a, some b => pEqual a b
  | _, _ => false
end

def pUnionContains (needle : PType) : PType → Prop
  | .union a b => needle = a ∨ pUnionContains needle b
  | candidate => needle = candidate

structure PTypeOps where
  egal : PType → PType → Bool
  subtype : PType → PType → Bool
  typeofParameter : PType → PType

def pIsType : PType → Bool
  | .bottom | .any | .unionAll .. | .union .. | .data .. | .typeEq .. | .typeEgal .. => true
  | _ => false

def pUnwrapVa : PType → PType
  | .vararg t _ => t
  | t => t

def pIsVararg : PType → Bool
  | .vararg .. => true
  | _ => false

def pFullVaLen (ps : List PType) : Nat × Bool :=
  match ps.getLast? with
  | none => (0, true)
  | some (.vararg _ (.int n)) => (ps.length + n - 1, true)
  | some (.vararg _ _) => (ps.length, false)
  | some _ => (ps.length, true)

/-- `isa(t, DataType)`. -/
def pIsDataType : PType → Bool
  | .any | .data .. | .typeEq _ | .typeEgal _ => true
  | _ => false

def typeassertDataTypeError : JlError :=
  .argumentError "TypeError: in typeassert, expected DataType"

/--
Julia source: base/promotion.jl:25-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _has_ancestor_typename(@nospecialize(a), name::Core.TypeName)
    @_foldable_meta
    @_nothrow_meta
    @_nospecializeinfer_meta
    a = a::DataType
    while true
        a.name === name && return true
        a === Any && return false
        a = supertype(a)::DataType
    end
end
```
-/
def hasAncestorTypename (a : PType) (name : TypeName) : Jl Bool :=
  match a with
  | .any => if anyTypeName = name then .ok true else .ok false
  | .data n _ _ super =>
      if n = name then .ok true
      else match super with
        | some s => if pIsDataType s then hasAncestorTypename s name
            else .error typeassertDataTypeError
        | none => .error typeassertDataTypeError
  | _ => .error typeassertDataTypeError

/- Supertype-chain name lookup used by the model of the builtin `<:`. -/
def pHasAncestorName : PType → TypeName → Bool
  | .any, name => anyTypeName = name
  | .data n _ _ super, name =>
      if n = name then true
      else match super with
        | some s => pHasAncestorName s name
        | none => false
  | _, _ => false

def pSubtype : PType → PType → Bool
  | _, .any => true
  | .bottom, _ => true
  | a, b =>
      match a, b with
      | .data an _ ap _, .data bn _ bp _ =>
          if an = bn then pListEqual ap bp else pHasAncestorName a bn
      | .union x y, b => pSubtype x b && pSubtype y b
      | a, .union x y => pSubtype a x || pSubtype a y
      | .typeVar _ upper, b => pSubtype upper b
      | .unionAll _ body, b => pSubtype body b
      | .typeEq x, .typeEq y => pSubtype x y
      | .typeEgal x, .typeEgal y => pSubtype x y
      | a, b => pEqual a b

def sourcePTypeOps : PTypeOps where
  egal := pEqual
  subtype := pSubtype
  typeofParameter := id

def pAscendToName : PType → TypeName → Option PType
  | t@(.data name _ _ super), target =>
      if name = target then some t
      else match super with
        | some s => if pIsDataType s then pAscendToName s target else none
        | none => none
  | t@(.any), target => if anyTypeName = target then some t else none
  | _, _ => none

def pJoinParamsLoop (ops : PTypeOps) :
    Nat → List PType → List PType → List PType → List PType → List PType × List PType
  | i, ai :: as, bi :: bs, params, vars =>
      if ops.egal ai bi ||
          (pIsType ai && pIsType bi && ops.subtype ai bi && ops.subtype bi ai) then
        pJoinParamsLoop ops (i + 1) as bs (params ++ [ai]) vars
      else
        let v := PType.typeVar i .any
        pJoinParamsLoop ops (i + 1) as bs (params ++ [v]) (v :: vars)
  | _, _, _, params, vars => (params, vars)

def pAbstractType : PType := .data ⟨"Core", "Type"⟩ "Type" [] (some .any)


/-! ## Promotion type machinery -/
/--
Julia source: base/promotion.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typejoin() = Bottom
```
-/
def typejoinZero : PType := .bottom

/--
Julia source: base/promotion.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typejoin(@nospecialize(t)) = (@_nospecializeinfer_meta; t)
```
-/
def typejoinOne (t : PType) : PType := t

/--
Julia source: base/promotion.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typejoin(@nospecialize(t), @nospecialize(s), @nospecialize(u)) = (@_foldable_meta; @_nospecializeinfer_meta; typejoin(typejoin(t, s), u))
```
-/
def typejoinThree (join : PType → PType → Option PType) (t s u : PType) : Option PType := do
  join (← join t s) u

/--
Julia source: base/promotion.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typejoin(@nospecialize(t), @nospecialize(s), @nospecialize(u), ts...) = (@_foldable_meta; @_nospecializeinfer_meta; afoldl(typejoin, typejoin(t, s, u), ts...))
```
-/
def typejoinMany (join : PType → PType → Option PType) (t s u : PType) (ts : List PType) :
    Option PType := do
  ts.foldlM join (← typejoinThree join t s u)


def pTailFrom (join : PType → PType → Option PType) (ps : List PType) (i : Nat) :
    Option PType :=
  if ps.length < i then some (pUnwrapVa (ps.getLastD .bottom))
  else (ps.drop (i - 1)).foldlM (fun t p => join t (pUnwrapVa p)) .bottom

def pJoinTuples (join : PType → PType → Option PType) (ap bp : List PType) :
    Option PType := do
  let lar := ap.length
  let lbr := bp.length
  if lar = 0 then
    return .data tupleTypeName "Tuple" [.vararg (← pTailFrom join bp 1) .open] (some .any)
  if lbr = 0 then
    return .data tupleTypeName "Tuple" [.vararg (← pTailFrom join ap 1) .open] (some .any)
  let av := pFullVaLen ap
  let bv := pFullVaLen bp
  let laf := av.1
  let lbf := bv.1
  let init : List PType × Nat ←
    if laf < lbf then
      if pIsVararg (ap.getLastD .bottom) && !av.2 then do
        let c := List.replicate laf .bottom
        let joined ← join (pUnwrapVa (ap.getLastD .bottom)) (← pTailFrom join bp laf)
        pure (if laf = 0 then c else c.set (laf - 1) (.vararg joined .open), laf - 1)
      else do
        let tail ← pTailFrom join bp (laf + 1)
        pure ((List.replicate (laf + 1) .bottom).set laf (.vararg tail .open), laf)
    else if lbf < laf then
      if pIsVararg (bp.getLastD .bottom) && !bv.2 then do
        let c := List.replicate lbf .bottom
        let joined ← join (pUnwrapVa (bp.getLastD .bottom)) (← pTailFrom join ap lbf)
        pure (if lbf = 0 then c else c.set (lbf - 1) (.vararg joined .open), lbf - 1)
      else do
        let tail ← pTailFrom join ap (lbf + 1)
        pure ((List.replicate (lbf + 1) .bottom).set lbf (.vararg tail .open), lbf)
    else pure (List.replicate laf .bottom, laf)
  let c ← (List.range init.2).foldlM (fun c j => do
    let ai := ap.getD (min j (lar - 1)) .bottom
    let bi := bp.getD (min j (lbr - 1)) .bottom
    let ci ← join (pUnwrapVa ai) (pUnwrapVa bi)
    pure (c.set j (if j + 1 = c.length && (pIsVararg ai || pIsVararg bi)
      then .vararg ci .open else ci))) init.1
  return .data tupleTypeName "Tuple" c (some .any)

/- The `while !(b === Any)` loop of `typejoin(a, b)` on two DataTypes; `none` when a
`::DataType` assertion fails. -/
def pJoinData (ops : PTypeOps) (a b : PType) : Option PType :=
  match b with
  | .any => some .any
  | .data bn _ bp bsup =>
      match hasAncestorTypename a bn with
      | .error _ => none
      | .ok true =>
          match pAscendToName a bn with
          | some aprimary@(.data an aw ap asup) =>
              if ap.length = 0 then some aprimary
              else
                let joined := pJoinParamsLoop ops 1 ap bp [] []
                some (joined.2.foldl (fun body v => .unionAll v body)
                  (.data an aw joined.1 asup))
          | some aprimary@(.any) => some aprimary
          | _ => none
      | .ok false =>
          match bsup with
          | some s => if pIsDataType s then pJoinData ops a s else none
          | none => none
  | _ => none

/--
Julia source: base/promotion.jl:37-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typejoin(@nospecialize(a), @nospecialize(b))
    @_foldable_meta
    @_nothrow_meta
    @_nospecializeinfer_meta
    if isa(a, TypeVar)
        return typejoin(a.ub, b)
    elseif isa(b, TypeVar)
        return typejoin(a, b.ub)
    elseif a === b
        return a
    elseif !isa(a, Type) || !isa(b, Type)
        return Any
    elseif a <: b
        return b
    elseif b <: a
        return a
    elseif isa(a, UnionAll)
        return UnionAll(a.var, typejoin(a.body, b))
    elseif isa(b, UnionAll)
        return UnionAll(b.var, typejoin(a, b.body))
    elseif isa(a, Union)
        return typejoin(typejoin(a.a, a.b), b)
    elseif isa(b, Union)
        return typejoin(a, typejoin(b.a, b.b))
    elseif isTypeEgal(a) || isTypeEgal(b)
        a = isTypeEgal(a) ? typeof(type_parameter(a)) : a
        b = isTypeEgal(b) ? typeof(type_parameter(b)) : b
        return typejoin(a, b)
    elseif isTypeEq(a) || isTypeEq(b)
        # At least one operand is a `Type{X}` kind. We have already ruled out
        # `a <: b`, `b <: a`, and any `UnionAll`/`Union`/`TypeVar`. The least supertype
        # of a `Type{X}` kind is the abstract `Type`, so widen each kind to `Type` and
        # join the two by subtyping. We compare directly instead of recursing through
        # `typejoin`, because `Type === (Type{T} where T)` would re-enter this branch and
        # not terminate.
        a = isTypeEq(a) ? Type : a
        b = isTypeEq(b) ? Type : b
        return a <: b ? b :
               b <: a ? a : Any
    end
    # a and b are DataTypes
    # We have to hide Constant info from inference, see #44390
    a, b = inferencebarrier(a)::DataType, inferencebarrier(b)::DataType
    if a.name === Tuple.name
        if !(b.name === Tuple.name)
            return Any
        end
        ap, bp = a.parameters, b.parameters
        lar = length(ap)
        lbr = length(bp)
        if lar == 0
            return Tuple{Vararg{tailjoin(bp, 1)}}
        end
        if lbr == 0
            return Tuple{Vararg{tailjoin(ap, 1)}}
        end
        laf, afixed = full_va_len(ap)
        lbf, bfixed = full_va_len(bp)
        if laf < lbf
            if isvarargtype(ap[lar]) && !afixed
                c = Vector{Any}(undef, laf)
                c[laf] = Vararg{typejoin(unwrapva(ap[lar]), tailjoin(bp, laf))}
                n = laf-1
            else
                c = Vector{Any}(undef, laf+1)
                c[laf+1] = Vararg{tailjoin(bp, laf+1)}
                n = laf
            end
        elseif lbf < laf
            if isvarargtype(bp[lbr]) && !bfixed
                c = Vector{Any}(undef, lbf)
                c[lbf] = Vararg{typejoin(unwrapva(bp[lbr]), tailjoin(ap, lbf))}
                n = lbf-1
            else
                c = Vector{Any}(undef, lbf+1)
                c[lbf+1] = Vararg{tailjoin(ap, lbf+1)}
                n = lbf
            end
        else
            c = Vector{Any}(undef, laf)
            n = laf
        end
        for i = 1:n
            ai = ap[min(i,lar)]; bi = bp[min(i,lbr)]
            ci = typejoin(unwrapva(ai), unwrapva(bi))
            c[i] = i == length(c) && (isvarargtype(ai) || isvarargtype(bi)) ? Vararg{ci} : ci
        end
        return Tuple{c...}
    elseif b.name === Tuple.name
        return Any
    end
    while !(b === Any)
        if _has_ancestor_typename(a, b.name)
            while !(a.name === b.name)
                a = supertype(a)::DataType
            end
            aprimary = a.name.wrapper
            # join on parameters
            n = length(a.parameters)
            if n == 0
                return aprimary
            end
            vars = []
            for i = 1:n
                ai, bi = a.parameters[i], b.parameters[i]
                if ai === bi || (isa(ai,Type) && isa(bi,Type) && ai <: bi && bi <: ai)
                    aprimary = aprimary{ai}
                else
                    aprimary = aprimary::UnionAll
                    # pushfirst!(vars, aprimary.var)
                    _growbeg!(vars, 1)
                    vars[1] = aprimary.var
                    aprimary = aprimary.body
                end
            end
            for v in vars
                aprimary = UnionAll(v, aprimary)
            end
            return aprimary
        end
        b = supertype(b)::DataType
    end
    return Any
end
```
-/
-- Source: base/promotion.jl:37-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def typejoinPairMethod (ops : PTypeOps) (join : PType → PType → Option PType)
    (a b : PType) : Option PType :=
  match a, b with
  | .typeVar _ upper, b => join upper b
  | a, .typeVar _ upper => join a upper
  | a, b =>
      if ops.egal a b then some a
      else if !pIsType a || !pIsType b then some .any
      else if ops.subtype a b then some b
      else if ops.subtype b a then some a
      else match a, b with
        | .unionAll v body, b => do return .unionAll v (← join body b)
        | a, .unionAll v body => do return .unionAll v (← join a body)
        | .union x y, b => do join (← join x y) b
        | a, .union x y => do join a (← join x y)
        | .typeEgal x, .typeEgal y =>
            join (ops.typeofParameter x) (ops.typeofParameter y)
        | .typeEgal x, b => join (ops.typeofParameter x) b
        | a, .typeEgal y => join a (ops.typeofParameter y)
        | .typeEq _, b =>
            let a := pAbstractType
            let b := match b with | .typeEq _ => pAbstractType | _ => b
            some (if ops.subtype a b then b else if ops.subtype b a then a else .any)
        | a, .typeEq _ =>
            let b := pAbstractType
            some (if ops.subtype a b then b else if ops.subtype b a then a else .any)
        | a@(.data an _ ap _), b@(.data bn _ bp _) =>
            if an = tupleTypeName then
              if bn = tupleTypeName then pJoinTuples join ap bp else some .any
            else if bn = tupleTypeName then some .any
            else pJoinData ops a b
        | _, _ => some .any

-- Source: base/promotion.jl:37-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def typejoinPair (ops : PTypeOps) (join : PType → PType → Option PType)
    (a b : PType) : Option PType :=
  typejoinPairMethod ops join a b

/-! Monotonicity of the tuple-join helpers and of the `typejoin(a, b)` body in the recursive
`typejoin` callee, so that `typejoin` is the least fixed point of its body (`partial_fixpoint`). -/
section TypejoinMonotone
open Lean.Order

theorem pTailFrom_monotone (ps : List PType) (i : Nat) :
    monotone (fun join : PType → PType → Option PType => pTailFrom join ps i) := by
  unfold pTailFrom
  repeat' monotonicity

@[partial_fixpoint_monotone]
theorem monotone_pTailFrom {γ : Type} [PartialOrder γ] (F : γ → PType → PType → Option PType)
    (ps : List PType) (i : Nat) (h : monotone F) :
    monotone (fun x => pTailFrom (F x) ps i) :=
  fun x y hxy => pTailFrom_monotone ps i _ _ (h x y hxy)

theorem pJoinTuples_monotone (ap bp : List PType) :
    monotone (fun join : PType → PType → Option PType => pJoinTuples join ap bp) := by
  unfold pJoinTuples
  repeat' monotonicity

@[partial_fixpoint_monotone]
theorem monotone_pJoinTuples {γ : Type} [PartialOrder γ] (F : γ → PType → PType → Option PType)
    (ap bp : List PType) (h : monotone F) :
    monotone (fun x => pJoinTuples (F x) ap bp) :=
  fun x y hxy => pJoinTuples_monotone ap bp _ _ (h x y hxy)

theorem typejoinPair_monotone (ops : PTypeOps) (a b : PType) :
    monotone (fun join : PType → PType → Option PType => typejoinPair ops join a b) := by
  unfold typejoinPair typejoinPairMethod
  repeat' monotonicity

@[partial_fixpoint_monotone]
theorem monotone_typejoinPair {γ : Type} [PartialOrder γ] (ops : PTypeOps)
    (F : γ → PType → PType → Option PType) (a b : PType) (h : monotone F) :
    monotone (fun x => typejoinPair ops (F x) a b) :=
  fun x y hxy => typejoinPair_monotone ops a b _ _ (h x y hxy)

end TypejoinMonotone

/- *dispatch*: `typejoin(a, b)` with the source subtype relation: the least fixed point of the
method body, so `none` exactly when the recursion never returns (Julia overflows its stack). -/
def typejoin (a b : PType) : Option PType :=
  typejoinPair sourcePTypeOps typejoin a b
partial_fixpoint

/--
Julia source: base/promotion.jl:166-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typesplit(@nospecialize(a), @nospecialize(b))
    @_foldable_meta
    @_nospecializeinfer_meta
    if a <: b
        return Bottom
    end
    if isa(a, Union)
        return Union{typesplit(a.a, b),
                     typesplit(a.b, b)}
    end
    return a
end
```
-/
def typesplit (ops : PTypeOps) : PType → PType → PType
  | a, b =>
      if ops.subtype a b then .bottom
      else match a with
        | .union x y => .union (typesplit ops x b) (typesplit ops y b)
        | _ => a

/--
Julia source: base/promotion.jl:198-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_typejoin(@nospecialize(a), @nospecialize(b))
    c = typejoin(_promote_typesubtract(a), _promote_typesubtract(b))
    return Union{a, b, c}
end
```
-/
def promoteTypejoin (join : PType → PType → Option PType) (subtract : PType → PType)
    (a b : PType) : Option PType := do
  let c ← join (subtract a) (subtract b)
  return .union a (.union b c)

/--
Julia source: base/promotion.jl:202-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_typesubtract(@nospecialize(a)) =
    a === Any ? a :
    a >: Union{Nothing, Missing} ? typesplit(a, Union{Nothing, Missing}) :
    a >: Nothing ? typesplit(a, Nothing) :
    a >: Missing ? typesplit(a, Missing) :
    a
```
-/
def promoteTypesubtract (ops : PTypeOps) (nothing missing a : PType) : PType :=
  if ops.egal a .any then a
  else if ops.subtype (.union nothing missing) a then typesplit ops a (.union nothing missing)
  else if ops.subtype nothing a then typesplit ops a nothing
  else if ops.subtype missing a then typesplit ops a missing
  else a

mutual
/--
Julia source: base/promotion.jl:209-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_typejoin_union(::Type{T}) where T
    if T === Union{}
        return Union{}
    elseif T isa UnionAll
        return Any # TODO: compute more precise bounds
    elseif T isa Union
        return promote_typejoin(promote_typejoin_union(T.a), promote_typejoin_union(T.b))
    elseif T isa DataType
        T <: Tuple && return typejoin_union_tuple(T)
        return T
    elseif isType(T)
        return T
    else
        error("unreachable") # not a type??
    end
end
```
-/
def promoteTypejoinUnionMethod {m : Type → Type} [Monad m]
    (promoteTypejoin : PType → PType → m PType)
    (promoteTypejoinUnion : PType → m PType) (typejoinUnionTuple : PType → m PType)
    (error : String → m PType) (T : PType) : m PType :=
  match T with
  | .bottom => pure .bottom
  | .unionAll _ _ => pure .any
  | .union a b => do
      promoteTypejoin (← promoteTypejoinUnion a) (← promoteTypejoinUnion b)
  | t@(.data n _ _ _) => if n = tupleTypeName then typejoinUnionTuple t else pure t
  | t@(.typeEq _) => pure t
  | t@(.typeEgal _) => pure t
  | .any => pure .any
  | _ => error "unreachable"

/--
Julia source: base/promotion.jl:226-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typejoin_union_tuple(T::DataType)
    @_foldable_meta
    p = T.parameters::Core.SimpleVector
    lr = length(p)
    if lr == 0
        return Tuple{}
    end
    c = Vector{Any}(undef, lr)
    for i = 1:lr
        pi = p[i]
        U = unwrapva(pi)
        if U === Union{}
            ci = Union{}
        elseif U isa Union
            ci = typejoin(U.a, U.b)
        elseif U isa UnionAll
            return Any # TODO: compute more precise bounds
        else
            ci = promote_typejoin_union(U)
        end
        if i == lr && isvarargtype(pi)
            c[i] = isdefined(pi, :N) ? Vararg{ci, pi.N} : Vararg{ci}
        else
            c[i] = ci
        end
    end
    return Base.rewrap_unionall(Tuple{c...}, T)
end
```
-/
def typejoinUnionTupleMethod {m : Type → Type} [Monad m] (join : PType → PType → m PType)
    (promoteUnion : PType → m PType) (rewrap : PType → List PType → PType)
    (noMethod : PType → m PType) (T : PType) : m PType :=
  let params? : Option (List PType) := match T with
    | .any => some []
    | .data _ _ params _ => some params
    | .typeEq p | .typeEgal p => some [p]
    | _ => none
  match params? with
  | none => noMethod T
  | some params =>
      if params.isEmpty then pure (.data tupleTypeName "Tuple" [] (some .any))
      else
        -- `none`: the loop returned `Any` early at a `UnionAll` parameter.
        let rec normalize (i : Nat) : List PType → m (Option (List PType))
          | [] => pure (some [])
          | p :: ps => do
              let U := pUnwrapVa p
              let ci? ← match U with
                | .bottom => pure (some PType.bottom)
                | .union a b => some <$> join a b
                | .unionAll .. => pure none
                | t => some <$> promoteUnion t
              match ci? with
              | none => pure none
              | some ci =>
                  let c := if i + 1 = params.length && pIsVararg p then
                    match p with | .vararg _ n => PType.vararg ci n | _ => ci
                    else ci
                  match ← normalize (i + 1) ps with
                  | some cs => pure (some (c :: cs))
                  | none => pure none
        do
          match ← normalize 0 params with
          | some cs => pure (rewrap T cs)
          | none => pure .any

end

/--
Julia source: base/promotion.jl:256-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function full_va_len(p::Core.SimpleVector)
    isempty(p) && return 0, true
    last = p[end]
    if isvarargtype(last)
        if isdefined(last, :N)
            N = last.N
            isa(N, Int) && return length(p) + N - 1, true
        end
        return length(p), false
    end
    return length(p), true
end
```
-/
def fullVaLen (p : List PType) : Nat × Bool :=
  if p.isEmpty then (0, true)
  else match p.getLast! with
    | .vararg _ (.int n) => (p.length + n - 1, true)
    | .vararg _ _ => (p.length, false)
    | _ => (p.length, true)

/--
Julia source: base/promotion.jl:270-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tailjoin(A::SimpleVector, i::Int)
    @_foldable_meta
    if i > length(A)
        return unwrapva(A[end])
    end
    t = Bottom
    for j = i:length(A)
        t = typejoin(t, unwrapva(A[j]))
    end
    return t
end
```
-/
def tailjoin {m : Type → Type} [Monad m] [MonadExceptOf JlError m]
    (join : PType → PType → m PType) (A : List PType) (i : Int) : m PType :=
  if Int.ofNat A.length < i then
    match A.getLast? with
    | some last => pure (pUnwrapVa last)
    | none => throw .boundsError
  else if i < 1 then throw .boundsError
  else (A.drop (i.toNat - 1)).foldlM (fun t a => join t (pUnwrapVa a)) .bottom

/--
Julia source: base/promotion.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type()  = Bottom
```
-/
def promoteTypeZero (bottom : α) : α := bottom

/--
Julia source: base/promotion.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(T) = T
```
-/
def promoteTypeOneGeneric (T : α) : α := T

/--
Julia source: base/promotion.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(T, S, U) = (@inline; promote_type(promote_type(T, S), U))
```
-/
def promoteTypeThree {m : Type → Type} [Monad m] (promoteType : α → α → m α) (T S U : α) :
    m α := do
  promoteType (← promoteType T S) U

/--
Julia source: base/promotion.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(T, S, U, V...) = (@inline; afoldl(promote_type, promote_type(T, S, U), V...))
```
-/
def promoteTypeMany {m : Type → Type} [Monad m] (promoteType : α → α → m α) (T S U : α)
    (Vs : List α) : m α := do
  Vs.foldlM promoteType (← promoteTypeThree promoteType T S U)

/--
Julia source: base/promotion.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(::Type{Bottom}, ::Type{Bottom}) = Bottom
```
-/
def promoteTypeBottomBottom (bottom : α) : α := bottom

/--
Julia source: base/promotion.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(::Type{T}, ::Type{T}) where {T} = T
```
-/
def promoteTypeSame (T : α) : α := T

/--
Julia source: base/promotion.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(::Type{T}, ::Type{Bottom}) where {T} = T
```
-/
def promoteTypeRightBottom (T : α) : α := T

/--
Julia source: base/promotion.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(::Type{Bottom}, ::Type{T}) where {T} = T
```
-/
def promoteTypeLeftBottom (T : α) : α := T

/--
Julia source: base/promotion.jl:336-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_type(::Type{T}, ::Type{S}) where {T,S}
    @inline
    # Try promote_rule in both orders. Typically only one is defined,
    # and there is a fallback returning Bottom below, so the common case is
    #   promote_type(T, S) =>
    #   promote_result(T, S, result, Bottom) =>
    #   typejoin(result, Bottom) => result
    promote_result(T, S, promote_rule(T,S), promote_rule(S,T))
end
```
-/
def promoteTypePair (promoteRule : α → α → α)
    (promoteResult : α → α → α → α → β) (T S : α) : β :=
  promoteResult T S (promoteRule T S) (promoteRule S T)

/--
Julia source: base/promotion.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type, ::Type) = Bottom
```
-/
def promoteRuleDefault (bottom : α) (_T _S : α) : α := bottom

/--
Julia source: base/promotion.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Bottom}, slurp...) = Bottom
```
-/
def promoteRuleBottomFirst (bottom : α) (_slurp : List α) : α := bottom

/--
Julia source: base/promotion.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Bottom}, ::Type{Bottom}, slurp...) = Bottom # not strictly necessary, since the next method would match unambiguously anyways
```
-/
def promoteRuleBottomBoth (bottom : α) (_slurp : List α) : α := bottom

/--
Julia source: base/promotion.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Bottom}, ::Type{T}, slurp...) where {T} = T
```
-/
def promoteRuleBottomThenType (_bottom T : α) (_slurp : List α) : α := T

/--
Julia source: base/promotion.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{T}, ::Type{Bottom}, slurp...) where {T} = T
```
-/
def promoteRuleTypeThenBottom (_bottom T : α) (_slurp : List α) : α := T

/--
Julia source: base/promotion.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_result(::Type,::Type,::Type{T},::Type{S}) where {T,S} = (@inline; promote_type(T,S))
```
-/
def promoteResultDefault (promoteType : α → α → β) (_T _S : α) (R1 R2 : α) : β :=
  promoteType R1 R2

/--
Julia source: base/promotion.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_result(::Type{T},::Type{S},::Type{Bottom},::Type{Bottom}) where {T,S} = (@inline; typejoin(T, S))
```
-/
def promoteResultNoRules (typejoin : α → α → β) (T S : α) (_R1 _R2 : α) : β :=
  typejoin T S

/-! ## Value computations

The value-level methods run in any monad `m`: `Jl` when every call returns or throws, and
`JlPartial` when a type computation they make (`promote_type`) may never return. -/

/-- A Julia computation that never returns (`none`), throws, or returns. -/
abbrev JlPartial := ExceptT JlError Option

section ValueComputations
variable {m : Type → Type} [Monad m]

/--
Julia source: base/promotion.jl:397-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _promote(x::T, y::S) where {T,S}
    @inline
    R = promote_type(T, S)
    return (convert(R, x), convert(R, y))
end
```
-/
def promotePairValues (promoteTypeof : α → β → m PType)
    (convertLeft : PType → α → m γ) (convertRight : PType → β → m γ)
    (x : α) (y : β) : m (γ × γ) := do
  let R ← promoteTypeof x y
  let px ← convertLeft R x
  let py ← convertRight R y
  pure (px, py)

/--
Julia source: base/promotion.jl:402-402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_typeof(x) = typeof(x)
```
-/
def promoteTypeofOne (typeOf : α → PType) (x : α) : PType := typeOf x

/--
Julia source: base/promotion.jl:403-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_typeof(x, y) = (@inline; promote_type(typeof(x), typeof(y)))
```
-/
def promoteTypeofTwo (typeOfLeft : α → PType) (typeOfRight : β → PType)
    (promoteType : PType → PType → m PType) (x : α) (y : β) : m PType :=
  promoteType (typeOfLeft x) (typeOfRight y)

/--
Julia source: base/promotion.jl:404-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_typeof(x, y, z) = (@inline; promote_type(typeof(x), typeof(y), typeof(z)))
```
-/
def promoteTypeofThree (typeOfFirst : α → PType) (typeOfSecond : β → PType)
    (typeOfThird : γ → PType) (promoteType : PType → PType → m PType)
    (x : α) (y : β) (z : γ) : m PType :=
  promoteTypeThree promoteType (typeOfFirst x) (typeOfSecond y) (typeOfThird z)

/--
Julia source: base/promotion.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_typeof(x, y, z, a...) = (@inline; afoldl(((::Type{T}, y) where {T}) -> promote_type(T, typeof(y)), promote_typeof(x, y, z), a...))
```
-/
def promoteTypeofMany {ι : Type} {V : ι → Type} (typeOfFirst : α → PType)
    (typeOfSecond : β → PType) (typeOfThird : γ → PType) (typeOfRest : Sigma V → PType)
    (promoteType : PType → PType → m PType)
    (x : α) (y : β) (z : γ) (a : List (Sigma V)) : m PType := do
  a.foldlM (fun acc value => promoteType acc (typeOfRest value))
    (← promoteTypeofThree typeOfFirst typeOfSecond typeOfThird promoteType x y z)

/--
Julia source: base/promotion.jl:406-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _promote(x, y, z)
    @inline
    R = promote_typeof(x, y, z)
    return (convert(R, x), convert(R, y), convert(R, z))
end
```
-/
def promoteTripleValues (promoteTypeof : α → β → γ → m PType)
    (convertFirst : PType → α → m δ) (convertSecond : PType → β → m δ)
    (convertThird : PType → γ → m δ) (x : α) (y : β) (z : γ) :
    m (δ × δ × δ) := do
  let R ← promoteTypeof x y z
  let px ← convertFirst R x
  let py ← convertSecond R y
  let pz ← convertThird R z
  pure (px, py, pz)

/--
Julia source: base/promotion.jl:411-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _promote(x, y, zs...)
    @inline
    R = promote_typeof(x, y, zs...)
    return (convert(R, x), convert(R, y), convert(Tuple{Vararg{R}}, zs)...)
end
```
-/
def promoteRestValues {ι : Type} {V : ι → Type}
    (promoteTypeof : α → β → List (Sigma V) → m PType)
    (convertFirst : PType → α → m δ) (convertSecond : PType → β → m δ)
    (convertTuple : PType → List (Sigma V) → m (List δ))
    (x : α) (y : β) (zs : List (Sigma V)) : m ((δ × δ) × List δ) := do
  let R ← promoteTypeof x y zs
  let px ← convertFirst R x
  let py ← convertSecond R y
  let pzs ← convertTuple (.data tupleTypeName "Tuple" [.vararg R .open] (some .any)) zs
  pure ((px, py), pzs)

/--
Julia source: base/promotion.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote() = ()
```
-/
def promoteEmpty : List α := []

/--
Julia source: base/promotion.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote(x) = (x,)
```
-/
def promoteSingle (x : α) : List α := [x]

/--
Julia source: base/promotion.jl:423-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote(x, y)
    @inline
    px, py = _promote(x, y)
    not_sametype((x,y), (px,py))
    px, py
end
```
-/
def promoteTwoValues (promote : α → β → m (γ × γ))
    (notSameType : α × β → γ × γ → m Unit) (x : α) (y : β) : m (γ × γ) := do
  let (px, py) ← promote x y
  notSameType (x, y) (px, py)
  pure (px, py)

/--
Julia source: base/promotion.jl:429-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote(x, y, z)
    @inline
    px, py, pz = _promote(x, y, z)
    not_sametype((x,y,z), (px,py,pz))
    px, py, pz
end
```
-/
def promoteThreeValues (promote : α → β → γ → m (δ × δ × δ))
    (notSameType : α × β × γ → δ × δ × δ → m Unit)
    (x : α) (y : β) (z : γ) : m (δ × δ × δ) := do
  let (px, py, pz) ← promote x y z
  notSameType (x, y, z) (px, py, pz)
  pure (px, py, pz)

/--
Julia source: base/promotion.jl:435-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote(x, y, z, a...)
    p = _promote(x, y, z, a...)
    not_sametype((x, y, z, a...), p)
    p
end
```
-/
def promoteManyValues {ι : Type} {V : ι → Type}
    (promote : α → β → γ → List (Sigma V) → m ((ε × ε) × List ε))
    (notSameType : (α × β × γ × List (Sigma V)) → (ε × ε × List ε) → m Unit)
    (x : α) (y : β) (z : γ) (a : List (Sigma V)) : m ((ε × ε) × List ε) := do
  let converted ← promote x y z a
  notSameType (x, y, z, a) (converted.1.1, converted.1.2, converted.2)
  pure converted

/--
Julia source: base/promotion.jl:441-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote(x::T, y::T, zs::T...) where {T} = (x, y, zs...)
```
-/
def promoteSameType (x y : α) (zs : List α) : List α := x :: y :: zs

/--
Julia source: base/promotion.jl:443-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
not_sametype(x::T, y::T) where {T} = sametype_error(x)
```
-/
def notSameTypeEqual (sametypeError : α → m Unit) (x _y : α) : m Unit :=
  sametypeError x

/--
Julia source: base/promotion.jl:445-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
not_sametype(x, y) = nothing
```
-/
def notSameTypeDifferent (_x : α) (_y : β) : m Unit := pure ()

/--
Julia source: base/promotion.jl:447-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sametype_error(input)
    @noinline
    error("promotion of types ",
          join(map(x->string(typeof(x)), input), ", ", " and "),
          " failed to change any arguments")
end
```
-/
def sametypeError [MonadExceptOf JlError m] (map : (α → String) → β → List String)
    (typeName : α → String) (join : List String → String → String → String)
    (error : String → JlError) (input : β) : m Unit :=
  throw (error ("promotion of types " ++ join (map typeName input) ", " " and " ++
    " failed to change any arguments"))


/--
Julia source: base/promotion.jl:454-454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Number, y::Number) = +(promote(x,y)...)
```
-/
def plusNumber (promote : α → α → m (β × β)) (plus : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  plus px py

/--
Julia source: base/promotion.jl:455-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Number, y::Number) = *(promote(x,y)...)
```
-/
def timesNumber (promote : α → α → m (β × β)) (times : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  times px py

/--
Julia source: base/promotion.jl:456-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Number, y::Number) = -(promote(x,y)...)
```
-/
def minusNumber (promote : α → α → m (β × β)) (minus : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  minus px py

/--
Julia source: base/promotion.jl:457-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(x::Number, y::Number) = /(promote(x,y)...)
```
-/
def divideNumber (promote : α → α → m (β × β)) (divide : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  divide px py

/--
Julia source: base/promotion.jl:459-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+%(x::Number, y::Number) = +%(promote(x,y)...)
```
-/
def plusWrapNumber (promote : α → α → m (β × β)) (plusWrap : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  plusWrap px py

/--
Julia source: base/promotion.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*%(x::Number, y::Number) = *%(promote(x,y)...)
```
-/
def timesWrapNumber (promote : α → α → m (β × β)) (timesWrap : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  timesWrap px py

/--
Julia source: base/promotion.jl:461-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(x::Number, y::Number) = -%(promote(x,y)...)
```
-/
def minusWrapNumber (promote : α → α → m (β × β)) (minusWrap : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  minusWrap px py

/--
Julia source: base/promotion.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::Number, y::Number) = ^(promote(x,y)...)
```
-/
def powerNumber (promote : α → α → m (β × β)) (power : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  power px py

/--
Julia source: base/promotion.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fma(x::Number, y::Number, z::Number) = fma(promote(x,y,z)...)
```
-/
def fmaNumber (promote : α → α → α → m (β × β × β))
    (fma : β → β → β → m γ) (x y z : α) : m γ := do
  let (px, py, pz) ← promote x y z
  fma px py pz

/--
Julia source: base/promotion.jl:510-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function muladd(a::Number, b::Number, c::Number)
    _a, _b, _c = promote(a, b, c)
    ((a === false) || (b === false)) && return _c
    return muladd(_a, _b, _c)
end
```
-/
def muladdNumber (promote : α → β → γ → m (δ × δ × δ))
    (muladd : δ → δ → δ → m δ)
    (isFalseFirst : α → Bool) (isFalseSecond : β → Bool)
    (a : α) (b : β) (c : γ) : m δ := do
  let (pa, pb, pc) ← promote a b c
  if isFalseFirst a || isFalseSecond b then pure pc else muladd pa pb pc

/--
Julia source: base/promotion.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Number, y::Number) = (==)(promote(x,y)...)
```
-/
def equalNumber (promote : α → β → m (γ × γ)) (equal : γ → γ → m δ)
    (x : α) (y : β) : m δ := do
  let (px, py) ← promote x y
  equal px py

/--
Julia source: base/promotion.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::Real, y::Real)     = (< )(promote(x,y)...)
```
-/
def lessNumber (promote : α → β → m (γ × γ)) (less : γ → γ → m δ)
    (x : α) (y : β) : m δ := do
  let (px, py) ← promote x y
  less px py

/--
Julia source: base/promotion.jl:518-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Real, y::Real)     = (<=)(promote(x,y)...)
```
-/
def lessEqualNumber (promote : α → β → m (γ × γ)) (lessEqual : γ → γ → m δ)
    (x : α) (y : β) : m δ := do
  let (px, py) ← promote x y
  lessEqual px py

/--
Julia source: base/promotion.jl:520-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Real, y::Real) = rem(promote(x,y)...)
```
-/
def remNumber (promote : α → α → m (β × β)) (rem : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  rem px py

/--
Julia source: base/promotion.jl:521-521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x::Real, y::Real) = mod(promote(x,y)...)
```
-/
def modNumber (promote : α → α → m (β × β)) (mod : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  mod px py

/--
Julia source: base/promotion.jl:522-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod1(x::Real, y::Real) = mod1(promote(x,y)...)
```
-/
def mod1Number (promote : α → α' → m (β × β)) (mod1 : β → β → m γ)
    (x : α) (y : α') : m γ := do
  let (px, py) ← promote x y
  mod1 px py

/--
Julia source: base/promotion.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld1(x::Real, y::Real) = cld(promote(x,y)...)
```
-/
def fld1Number (promote : α → α → m (β × β)) (cld : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  cld px py

/--
Julia source: base/promotion.jl:525-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::Real, y::Real) = max(promote(x,y)...)
```
-/
def maxNumber (promote : α → α → m (β × β)) (max : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  max px py

/--
Julia source: base/promotion.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::Real, y::Real) = min(promote(x,y)...)
```
-/
def minNumber (promote : α → α → m (β × β)) (min : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  min px py

/--
Julia source: base/promotion.jl:527-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax(x::Real, y::Real) = minmax(promote(x, y)...)
```
-/
def minmaxNumber (promote : α → α → m (β × β)) (minmax : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  minmax px py

end ValueComputations

/- `p === Union{}`. -/
def pIsBottom : PType → Bool
  | .bottom => true
  | _ => false

/--
Julia source: base/promotion.jl:529-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TupleOrBottom(tt...)
    any(p -> p === Union{}, tt) && return Union{}
    return Tuple{tt...}
end
```
-/
def tupleOrBottom (types : List PType) : PType :=
  if types.any pIsBottom
    then .bottom else .data tupleTypeName "Tuple" types (some .any)

/--
Julia source: base/promotion.jl:641-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_op(f, S::Type...)
    argT = TupleOrBottom(S...)
    argT === Union{} && return Union{}
    return _return_type(f, argT)
end
```
-/
def promoteOp (tupleOrBottom : List PType → PType)
    (returnType : α → PType → PType) (f : α) (S : List PType) : PType :=
  let argT := tupleOrBottom S
  match argT with
  | .bottom => .bottom
  | _ => returnType f argT

/--
Julia source: base/promotion.jl:650-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
no_op_err(name, T) = error(name," not defined for ",T)
```
-/
def noOpErr (typeName : α → String) (error : String → β) (name : String) (T : α) : β :=
  error (name ++ " not defined for " ++ typeName T)

/--
Julia source: base/promotion.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(+)(x::T, y::T) where {T<:Number} = no_op_err("+", T)
```
-/
def plusFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "+" T

/--
Julia source: base/promotion.jl:652-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(*)(x::T, y::T) where {T<:Number} = no_op_err("*", T)
```
-/
def timesFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "*" T

/--
Julia source: base/promotion.jl:653-653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::T, y::T) where {T<:Number} = no_op_err("-", T)
```
-/
def minusFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "-" T

/--
Julia source: base/promotion.jl:654-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(/)(x::T, y::T) where {T<:Number} = no_op_err("/", T)
```
-/
def divideFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "/" T

/--
Julia source: base/promotion.jl:655-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(^)(x::T, y::T) where {T<:Number} = no_op_err("^", T)
```
-/
def powerFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "^" T

/--
Julia source: base/promotion.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fma(x::T, y::T, z::T) where {T<:Number} = no_op_err("fma", T)
```
-/
def fmaFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "fma" T

/--
Julia source: base/promotion.jl:658-658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fma(x::Integer, y::Integer, z::Integer) = x*y+z
```
-/
def fmaIntegerFallback (mul add : α → α → α) (x y z : α) : α := add (mul x y) z

/--
Julia source: base/promotion.jl:659-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(x::T, y::T, z::T) where {T<:Number} = x*y+z
```
-/
def muladdFallback (mul add : α → α → α) (x y z : α) : α := add (mul x y) z

/--
Julia source: base/promotion.jl:661-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(x::T, y::T) where {T<:Integer} = no_op_err("&", T)
```
-/
def andFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "&" T

/--
Julia source: base/promotion.jl:662-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(x::T, y::T) where {T<:Integer} = no_op_err("|", T)
```
-/
def orFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "|" T

/--
Julia source: base/promotion.jl:663-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(x::T, y::T) where {T<:Integer} = no_op_err("xor", T)
```
-/
def xorFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "xor" T

/--
Julia source: base/promotion.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(==)(x::T, y::T) where {T<:Number} = x === y
```
-/
def equalFallback (identical : α → α → Bool) (x y : α) : Jl Bool := pure (identical x y)

/--
Julia source: base/promotion.jl:666-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(< )(x::T, y::T) where {T<:Real} = no_op_err("<" , T)
```
-/
def lessFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "<" T

/--
Julia source: base/promotion.jl:667-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<=)(x::T, y::T) where {T<:Real} = (x == y) | (x < y)
```
-/
def lessEqualFallback (equal less : α → α → Jl Bool) (x y : α) : Jl Bool := do
  let same ← equal x y
  let below ← less x y
  pure (same || below)

/--
Julia source: base/promotion.jl:669-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::T, y::T) where {T<:Real} = no_op_err("rem", T)
```
-/
def remFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "rem" T

/--
Julia source: base/promotion.jl:670-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x::T, y::T) where {T<:Real} = no_op_err("mod", T)
```
-/
def modFallback (noOpErr : String → α → β) (T : α) : β := noOpErr "mod" T

/--
Julia source: base/promotion.jl:672-672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::Real) = x
```
-/
def minUnary (x : α) : α := x

/--
Julia source: base/promotion.jl:673-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::Real) = x
```
-/
def maxUnary (x : α) : α := x

/--
Julia source: base/promotion.jl:674-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax(x::Real) = (x, x)
```
-/
def minmaxUnary (x : α) : α × α := (x, x)

/--
Julia source: base/promotion.jl:676-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::T, y::T) where {T<:Real} = ifelse(y < x, x, y)
```
-/
def maxSameType (less : α → α → Jl Bool) (x y : α) : Jl α := do
  let yLessThanX ← less y x
  pure (if yLessThanX then x else y)

/--
Julia source: base/promotion.jl:677-677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::T, y::T) where {T<:Real} = ifelse(y < x, y, x)
```
-/
def minSameType (less : α → α → Jl Bool) (x y : α) : Jl α := do
  let yLessThanX ← less y x
  pure (if yLessThanX then y else x)

/--
Julia source: base/promotion.jl:678-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax(x::T, y::T) where {T<:Real} = y < x ? (y, x) : (x, y)
```
-/
def minmaxSameType (less : α → α → Jl Bool) (x y : α) : Jl (α × α) := do
  let yLessThanX ← less y x
  pure (if yLessThanX then (y, x) else (x, y))

/--
Julia source: base/promotion.jl:680-680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::T, y::T) where {T<:Signed} = no_op_err("flipsign", T)
```
-/
def flipsignFallback (noOpErr : String → α → β) (T : α) : β :=
  noOpErr "flipsign" T

/-! ## Concrete primitive dispatch -/

inductive PrimitiveType where
  | bool
  | int (t : IntTy)
  | float (t : JuliaLean.base.float.FTy)
  deriving DecidableEq, Repr

def primitiveValueType : PrimitiveType → Type
  | .bool => Bool
  | .int t => JInt t
  | .float t => JuliaLean.base.float.FV t

abbrev PrimitiveInput := Sigma primitiveValueType

def pPromotionNumber : PType := .data ⟨"Core", "Number"⟩ "Number" [] (some .any)
def pPromotionReal : PType := .data ⟨"Core", "Real"⟩ "Real" [] (some pPromotionNumber)
def pPromotionInteger : PType :=
  .data ⟨"Core", "Integer"⟩ "Integer" [] (some pPromotionReal)
def pPromotionSigned : PType :=
  .data ⟨"Core", "Signed"⟩ "Signed" [] (some pPromotionInteger)
def pPromotionUnsigned : PType :=
  .data ⟨"Core", "Unsigned"⟩ "Unsigned" [] (some pPromotionInteger)
def pPromotionAbstractFloat : PType :=
  .data ⟨"Core", "AbstractFloat"⟩ "AbstractFloat" [] (some pPromotionReal)

def primitiveIntName : IntTy → String
  | .i8 => "Int8" | .i16 => "Int16" | .i32 => "Int32" | .i64 => "Int64" | .i128 => "Int128"
  | .u8 => "UInt8" | .u16 => "UInt16" | .u32 => "UInt32" | .u64 => "UInt64" | .u128 => "UInt128"

def primitiveFloatName : JuliaLean.base.float.FTy → String
  | .f16 => "Float16" | .f32 => "Float32" | .f64 => "Float64"

def primitivePType : PrimitiveType → PType
  | .bool => .data ⟨"Core", "Bool"⟩ "Bool" [] (some pPromotionInteger)
  | .int t => .data ⟨"Core", primitiveIntName t⟩ (primitiveIntName t) []
      (some (if t.signed then pPromotionSigned else pPromotionUnsigned))
  | .float t => .data ⟨"Core", primitiveFloatName t⟩ (primitiveFloatName t) []
      (some pPromotionAbstractFloat)

def primitiveValueTypeTag (t : PrimitiveType) (_ : primitiveValueType t) : PType :=
  primitivePType t

def primitiveTypeOfPType : PType → Option PrimitiveType
  | .data ⟨"Core", "Bool"⟩ _ [] _ => some .bool
  | .data ⟨"Core", "Int8"⟩ _ [] _ => some (.int .i8)
  | .data ⟨"Core", "Int16"⟩ _ [] _ => some (.int .i16)
  | .data ⟨"Core", "Int32"⟩ _ [] _ => some (.int .i32)
  | .data ⟨"Core", "Int64"⟩ _ [] _ => some (.int .i64)
  | .data ⟨"Core", "Int128"⟩ _ [] _ => some (.int .i128)
  | .data ⟨"Core", "UInt8"⟩ _ [] _ => some (.int .u8)
  | .data ⟨"Core", "UInt16"⟩ _ [] _ => some (.int .u16)
  | .data ⟨"Core", "UInt32"⟩ _ [] _ => some (.int .u32)
  | .data ⟨"Core", "UInt64"⟩ _ [] _ => some (.int .u64)
  | .data ⟨"Core", "UInt128"⟩ _ [] _ => some (.int .u128)
  | .data ⟨"Core", "Float16"⟩ _ [] _ => some (.float .f16)
  | .data ⟨"Core", "Float32"⟩ _ [] _ => some (.float .f32)
  | .data ⟨"Core", "Float64"⟩ _ [] _ => some (.float .f64)
  | _ => none

def primitiveBoolRuleWitness (t : PrimitiveType) :
    {r : PrimitiveType // primitiveValueType r =
      JuliaLean.base.bool.promoteRuleBool (primitiveValueType t)} :=
  match t with
  | .bool => ⟨.bool, rfl⟩
  | .int s => ⟨.int s, rfl⟩
  | .float f => ⟨.float f, rfl⟩

/- *dispatch*: `promote_rule(T, S)`. The Bottom methods of this file come first; `userRule`
stands for the methods that later-loaded files and packages add (`none` when no such method
matches), and the `promote_rule(::Type, ::Type)` fallback applies otherwise. -/
def promoteRuleDispatch (userRule : PType → PType → Option PType) (T S : PType) : PType :=
  match T, S with
  | .bottom, .bottom => promoteRuleBottomBoth .bottom []
  | .bottom, s => promoteRuleBottomThenType .bottom s []
  | t, .bottom => promoteRuleTypeThenBottom .bottom t []
  | _, _ =>
      match userRule T S with
      | some r => r
      | none => promoteRuleDefault .bottom T S

/-! Monotonicity of the `promote_type` methods in their recursive callee, for
`partial_fixpoint`. -/
section PromoteTypeMonotone
open Lean.Order

@[partial_fixpoint_monotone]
theorem monotone_promoteResultDefault {γ α β : Type} [PartialOrder γ] [PartialOrder β]
    (F : γ → α → α → β) (T S R1 R2 : α) (h : monotone F) :
    monotone (fun x => promoteResultDefault (F x) T S R1 R2) :=
  monotone_apply R2 _ (monotone_apply R1 F h)

@[partial_fixpoint_monotone]
theorem monotone_promoteTypePair {γ α β : Type} [PartialOrder γ] [PartialOrder β]
    (promoteRule : α → α → α) (F : γ → α → α → α → α → β) (T S : α) (h : monotone F) :
    monotone (fun x => promoteTypePair promoteRule (F x) T S) :=
  monotone_apply (promoteRule S T) _ (monotone_apply (promoteRule T S) _
    (monotone_apply S _ (monotone_apply T F h)))

end PromoteTypeMonotone

mutual
  /- *dispatch*: `promote_result(T, S, R1, R2)`. -/
  def promoteResultDispatch (userRule : PType → PType → Option PType)
      (T S R1 R2 : PType) : Option PType :=
    match R1, R2 with
    | .bottom, .bottom => promoteResultNoRules typejoin T S R1 R2
    | _, _ => promoteResultDefault (promoteTypeDispatch userRule) T S R1 R2
  partial_fixpoint

  /- *dispatch*: `promote_type(T, S)`: the least fixed point of the methods, so `none` exactly
  when the recursion through `promote_result` never returns. -/
  def promoteTypeDispatch (userRule : PType → PType → Option PType) (T S : PType) :
      Option PType :=
    match T, S with
    | .bottom, .bottom => some (promoteTypeBottomBottom .bottom)
    | t, .bottom => some (promoteTypeRightBottom t)
    | .bottom, s => some (promoteTypeLeftBottom s)
    | t, s =>
        if pEqual t s then some (promoteTypeSame t)
        else if !pIsType t || !pIsType s then some .any
        else
          promoteTypePair (promoteRuleDispatch userRule)
            (promoteResultDispatch userRule) t s
  partial_fixpoint
end

/- *dispatch*: `promote_type(T, S)` for the promotion rules `userRule`. -/
def promoteType (userRule : PType → PType → Option PType) (T S : PType) : Option PType :=
  promoteTypeDispatch userRule T S

/- *dispatch*: `promote_type(T, S)` called from a value computation. -/
def promoteTypeValue (userRule : PType → PType → Option PType) (T S : PType) :
    JlPartial PType :=
  ExceptT.lift (promoteType userRule T S)

/- *dispatch*: `promote_typeof(x, y, zs...)`, selecting the method by the number of values. -/
def promoteTypeofRest {m : Type → Type} [Monad m] {ι : Type} {V : ι → Type}
    (typeOf : Sigma V → PType) (promoteType : PType → PType → m PType) (x y : Sigma V)
    (zs : List (Sigma V)) : m PType :=
  match zs with
  | [] => promoteTypeofTwo typeOf typeOf promoteType x y
  | [z] => promoteTypeofThree typeOf typeOf typeOf promoteType x y z
  | z :: w :: rest => promoteTypeofMany typeOf typeOf typeOf typeOf promoteType x y z (w :: rest)

/- The `promote_rule` methods of `base/bool.jl`, `base/int.jl` and `base/float.jl`. -/
def primitivePromoteRule (T S : PType) : Option PType :=
  match primitiveTypeOfPType T, primitiveTypeOfPType S with
  | some .bool, some s => some (primitivePType (primitiveBoolRuleWitness s).val)
  | some (.int t), some (.int s) =>
      match JuliaLean.base.int.promote_rule t s with
      | some r => some (primitivePType (.int r))
      | none => none
  | some (.float t), some (.int s) =>
      some (primitivePType (.float (JuliaLean.base.float.promote_rule_float_int t s)))
  | some (.float t), some (.float s) =>
      match JuliaLean.base.float.promote_rule_float t s with
      | some r => some (primitivePType (.float r))
      | none => none
  | some (.float t), some .bool =>
      some (primitivePType (.float (JuliaLean.base.float.promote_rule_float_Bool t)))
  | _, _ => none

def primitiveNothingType : PType := .data ⟨"Core", "Nothing"⟩ "Nothing" [] (some .any)
def primitiveMissingType : PType := .data ⟨"Base", "Missing"⟩ "Missing" [] (some .any)

/- *dispatch*: `_promote_typesubtract(a)`. -/
def primitivePromoteTypesubtractDispatch (a : PType) : PType :=
  promoteTypesubtract sourcePTypeOps primitiveNothingType primitiveMissingType a

/- *dispatch*: `promote_typejoin(a, b)`. -/
def primitivePromoteTypejoinDispatch (a b : PType) : Option PType :=
  promoteTypejoin typejoin primitivePromoteTypesubtractDispatch a b

def primitivePromoteType (T S : PType) : Option PType :=
  promoteType primitivePromoteRule T S

def primitivePromoteTypeValue (T S : PType) : JlPartial PType :=
  promoteTypeValue primitivePromoteRule T S

def primitiveInputType (x : PrimitiveInput) : PType :=
  primitivePType x.1

/- `x === false` for a primitive value. -/
def primitiveEgalFalse : PrimitiveInput → Bool
  | ⟨.bool, b⟩ => !b
  | _ => false

/- *dispatch*: `not_sametype((x, y), (px, py))` on the runtime types of the two tuples. -/
def notSameTypePairDispatch {m : Type → Type} [Monad m] {ι : Type} {V : ι → Type}
    (typeOf : Sigma V → PType) (sametypeError : Sigma V × Sigma V → m Unit)
    (xs ys : Sigma V × Sigma V) : m Unit :=
  if pEqual (typeOf xs.1) (typeOf ys.1) && pEqual (typeOf xs.2) (typeOf ys.2) then
    notSameTypeEqual sametypeError xs ys
  else notSameTypeDifferent xs ys

/- *dispatch*: `not_sametype((x, y, z), (px, py, pz))` on the runtime types of the tuples. -/
def notSameTypeTripleDispatch {m : Type → Type} [Monad m] {ι : Type} {V : ι → Type}
    (typeOf : Sigma V → PType) (sametypeError : Sigma V × Sigma V × Sigma V → m Unit)
    (xs ys : Sigma V × Sigma V × Sigma V) : m Unit :=
  if pEqual (typeOf xs.1) (typeOf ys.1) && pEqual (typeOf xs.2.1) (typeOf ys.2.1) &&
      pEqual (typeOf xs.2.2) (typeOf ys.2.2) then
    notSameTypeEqual sametypeError xs ys
  else notSameTypeDifferent xs ys


/- *dispatch*: four-value BitInteger promotion `promote(x, y, z, w)` (`base/promotion.jl:411-415,435-441`).
Selects the homogeneous fast path `promoteSameType` when all four input types coincide, and
otherwise dispatches through `promoteManyValues` and `promoteRestValues` (`_promote`) to compute the
common type across all four operands and convert them in argument order. -/
def promoteFourBitIntegers {tx ty tz tw : IntTy}
    (x : JInt tx) (y : JInt ty) (z : JInt tz) (w : JInt tw) :
    Jl (JInt (((tx.promote ty).promote tz).promote tw) ×
        JInt (((tx.promote ty).promote tz).promote tw) ×
        JInt (((tx.promote ty).promote tz).promote tw) ×
        JInt (((tx.promote ty).promote tz).promote tw)) := do
  let p := ((tx.promote ty).promote tz).promote tw
  if hsame : tx = p ∧ ty = p ∧ tz = p ∧ tw = p then
    let xp : JInt p := hsame.1 ▸ x
    let yp : JInt p := hsame.2.1 ▸ y
    let zp : JInt p := hsame.2.2.1 ▸ z
    let wp : JInt p := hsame.2.2.2 ▸ w
    match promoteSameType xp yp [zp, wp] with
    | [a, b, c, d] => pure (a, b, c, d)
    | _ => .error (.methodError "promote")
  else
    let pty := primitivePType (.int p)
    let convertOne : {s : IntTy} → PType → JInt s → Jl (JInt p) := fun _ v =>
      JuliaLean.base.int.convert p v
    let convertRest : PType → List (Sigma JInt) → Jl (List (JInt p)) := fun _ xs =>
      xs.mapM (fun ⟨_, v⟩ => JuliaLean.base.int.convert p v)
    let promoteStep := fun (a : JInt tx) (b : JInt ty) (c : JInt tz) (rest : List (Sigma JInt)) =>
      promoteRestValues (m := Jl) (V := JInt)
        (fun _ _ _ => pure pty) convertOne convertOne convertRest a b (⟨tz, c⟩ :: rest)
    let notSame : (JInt tx × JInt ty × JInt tz × List (Sigma JInt)) →
        (JInt p × JInt p × List (JInt p)) → Jl Unit := fun orig prom =>
      if tx == p && ty == p && tz == p && tw == p then
        notSameTypeEqual (fun _ => .error (.argumentError "promotion of types failed to change any arguments")) orig orig
      else
        notSameTypeDifferent orig prom
    let ((px, py), rest) ← promoteManyValues (m := Jl) (V := JInt) promoteStep notSame x y z [⟨tw, w⟩]
    match rest with
    | [pz, pw] => pure (px, py, pz, pw)
    | _ => .error (.methodError "promote")
end JuliaLean.base.promotion

namespace JuliaLean.NumbersCov

open JuliaLean

namespace PromotionModel

/-! A source-shaped type-object model for `typejoin`. Unlike the compact `Ty`
model used below for numeric promotion tables, this keeps TypeVar bounds,
UnionAll binders, DataType supertypes and parameters, tuple Varargs, TypeEq and
TypeEgal distinct. -/

inductive PType where
  | bottom
  | any
  | typeVar (id : Nat) (upper : PType)
  | unionAll (var body : PType)
  | union (left right : PType)
  | data (name wrapper : String) (params : List PType) (super : Option PType)
  | typeEq (parameter : PType)
  | typeEgal (parameter : PType)
  | vararg (element : PType) (length : Option Nat)
  | parameter (tag : String)
  deriving Repr, Inhabited

structure PTypeOps where
  egal : PType → PType → Bool
  subtype : PType → PType → Bool
  typeofParameter : PType → PType

def pIsType : PType → Bool
  | .bottom | .any | .unionAll .. | .union .. | .data .. | .typeEq .. | .typeEgal .. => true
  | _ => false

def pUnwrapVa : PType → PType
  | .vararg t _ => t
  | t => t

def pIsVararg : PType → Bool
  | .vararg .. => true
  | _ => false

def pFullVaLen (ps : List PType) : Nat × Bool :=
  match ps.getLast? with
  | none => (0, true)
  | some (.vararg _ (some n)) => (ps.length + n - 1, true)
  | some (.vararg _ none) => (ps.length, false)
  | some _ => (ps.length, true)

def pHasAncestorName : PType → String → Bool
  | .data name _ _ super, target =>
      if name = target then true
      else match super with
        | some s => pHasAncestorName s target
        | none => false
  | _, _ => false

def pAscendToName : PType → String → Option PType
  | t@(.data name _ _ super), target =>
      if name = target then some t
      else match super with
        | some s => pAscendToName s target
        | none => none
  | _, _ => none

def pReplaceMismatchedParams (ops : PTypeOps) : List PType → List PType → List PType
  | a :: as, b :: bs =>
      (if ops.egal a b || (ops.subtype a b && ops.subtype b a) then a
       else .parameter "_") :: pReplaceMismatchedParams ops as bs
  | _, _ => []

def pJoinParams (ops : PTypeOps) : Nat → List PType → List PType → List PType × List PType
  | _, [], _ | _, _, [] => ([], [])
  | i, a :: as, b :: bs =>
      let rest := pJoinParams ops (i + 1) as bs
      if ops.egal a b || (ops.subtype a b && ops.subtype b a) then
        (a :: rest.1, rest.2)
      else
        let v := PType.typeVar i .any
        (v :: rest.1, v :: rest.2)

mutual
/-- `typejoin(a,b)` in `base/promotion.jl:37-160`. Fuel bounds traversal of
recursive Union and UnionAll graphs; Julia's runtime type graph is finite. -/
def pTypejoin (ops : PTypeOps) : Nat → PType → PType → PType
  | 0, _, _ => .any
  | fuel + 1, .typeVar _ ub, b => pTypejoin ops fuel ub b
  | fuel + 1, a, .typeVar _ ub => pTypejoin ops fuel a ub
  | fuel + 1, a, b =>
      if ops.egal a b then a
      else if !pIsType a || !pIsType b then .any
      else if ops.subtype a b then b
      else if ops.subtype b a then a
      else match a, b with
        | .unionAll v body, b => .unionAll v (pTypejoin ops fuel body b)
        | a, .unionAll v body => .unionAll v (pTypejoin ops fuel a body)
        | .union x y, b => pTypejoin ops fuel (pTypejoin ops fuel x y) b
        | a, .union x y => pTypejoin ops fuel a (pTypejoin ops fuel x y)
        | .typeEgal x, b => pTypejoin ops fuel (ops.typeofParameter x) b
        | a, .typeEgal y => pTypejoin ops fuel a (ops.typeofParameter y)
        | .typeEq _, b =>
            let a := pAbstractType
            let b := match b with | .typeEq _ => pAbstractType | _ => b
            if ops.subtype a b then b else if ops.subtype b a then a else .any
        | a, .typeEq _ =>
            let b := pAbstractType
            if ops.subtype a b then b else if ops.subtype b a then a else .any
        | a@(.data an _aw ap _asup), b@(.data bn _bw bp _bsup) =>
            if an = "Tuple" then
              if bn = "Tuple" then pJoinTuples ops fuel ap bp else .any
            else if bn = "Tuple" then .any
            else pJoinData ops fuel a b
        | _, _ => .any

/-- Join the tuple parameter vectors at `base/promotion.jl:80-124`, including
empty tuples, fixed/open Vararg lengths, unequal expanded lengths, tail joins,
and the final-slot Vararg rule. -/
def pJoinTuples (ops : PTypeOps) (fuel : Nat) (ap bp : List PType) : PType :=
  let lar := ap.length
  let lbr := bp.length
  if lar = 0 then
    .data "Tuple" "Tuple" [.vararg (pTailFrom ops fuel bp 1) none] (some .any)
  else if lbr = 0 then
    .data "Tuple" "Tuple" [.vararg (pTailFrom ops fuel ap 1) none] (some .any)
  else
    let av := pFullVaLen ap
    let bv := pFullVaLen bp
    let laf := av.1
    let lbf := bv.1
    let init : List PType × Nat :=
      if laf < lbf then
        if pIsVararg (ap.getLastD .bottom) && !av.2 then
          let c := List.replicate laf .bottom
          let joined := pTypejoin ops fuel (pUnwrapVa (ap.getLastD .bottom))
            (pTailFrom ops fuel bp laf)
          (if laf = 0 then c else c.set (laf - 1) (.vararg joined none), laf - 1)
        else
          let c := (List.replicate (laf + 1) .bottom).set laf
            (.vararg (pTailFrom ops fuel bp (laf + 1)) none)
          (c, laf)
      else if lbf < laf then
        if pIsVararg (bp.getLastD .bottom) && !bv.2 then
          let c := List.replicate lbf .bottom
          let joined := pTypejoin ops fuel (pUnwrapVa (bp.getLastD .bottom))
            (pTailFrom ops fuel ap lbf)
          (if lbf = 0 then c else c.set (lbf - 1) (.vararg joined none), lbf - 1)
        else
          let c := (List.replicate (lbf + 1) .bottom).set lbf
            (.vararg (pTailFrom ops fuel ap (lbf + 1)) none)
          (c, lbf)
      else (List.replicate laf .bottom, laf)
    let c := (List.range init.2).foldl (fun c j =>
      let ai := ap.getD (min j (lar - 1)) .bottom
      let bi := bp.getD (min j (lbr - 1)) .bottom
      let ci := pTypejoin ops fuel (pUnwrapVa ai) (pUnwrapVa bi)
      c.set j (if j + 1 = c.length && (pIsVararg ai || pIsVararg bi)
        then .vararg ci none else ci)) init.1
    .data "Tuple" "Tuple" c (some .any)

/-- Ordinary DataType ancestry loop and invariant-parameter join at
`base/promotion.jl:128-159`. -/
def pJoinData (ops : PTypeOps) (fuel : Nat) (a b : PType) : PType :=
  match fuel, b with
  | 0, _ => .any
  | _, .any => .any
  | fuel + 1, .data bn bw bp bsup =>
      if pHasAncestorName a bn then
        match pAscendToName a bn with
        | some (.data _ _ ap asup) =>
            let joined := pJoinParams ops 1 ap bp
            joined.2.foldr (fun v body => .unionAll v body)
              (.data bn bw joined.1 asup)
        | _ => .any
      else match bsup with
        | some s => pJoinData ops fuel a s
        | none => .any
  | _, _ => .any

def pTailFrom (ops : PTypeOps) (fuel : Nat) (ps : List PType) (i : Nat) : PType :=
  if ps.length < i then pUnwrapVa (ps.getLastD .bottom)
  else (ps.drop (i - 1)).foldl (pTypejoin ops fuel) .bottom

/-- The abstract `Type` kind used when widening TypeEq operands;
`base/promotion.jl:65-75`. -/
def pAbstractType : PType := .data "Type" "Type" [] (some .any)
end

def pTypejoin0 : PType := .bottom
def pTypejoin1 (t : PType) : PType := t
def pTypejoin3 (ops : PTypeOps) (a b c : PType) : PType :=
  pTypejoin ops 64 (pTypejoin ops 64 a b) c
def pTypejoinMany (ops : PTypeOps) (a b c : PType) (ts : List PType) : PType :=
  ts.foldl (pTypejoin ops 64) (pTypejoin3 ops a b c)

def pTypesplit (ops : PTypeOps) : PType → PType → PType
  | a, b => if ops.subtype a b then .bottom else match a with
    | .union x y => .union (pTypesplit ops x b) (pTypesplit ops y b)
    | _ => a

def pPromoteTypesubtract (ops : PTypeOps) (nothing missing : PType) (a : PType) : PType :=
  if ops.egal a .any then a
  else if ops.subtype (.union nothing missing) a then pTypesplit ops a (.union nothing missing)
  else if ops.subtype nothing a then pTypesplit ops a nothing
  else if ops.subtype missing a then pTypesplit ops a missing
  else a

def pPromoteTypejoin (ops : PTypeOps) (a b : PType) : PType :=
  .union a (.union b (pTypejoin ops 64 a b))

def pTypejoinUnionParamsWith (ops : PTypeOps) (fuel : Nat) (recur : PType → PType) :
    List PType → Option (List PType)
  | [] => some []
  | p :: ps =>
      let u := pUnwrapVa p
      let ci := match u with
        | .bottom => some PType.bottom
        | .union a b => some (pTypejoin ops fuel a b)
        | .unionAll .. => none
        | t => some (recur t)
      match ci, pTypejoinUnionParamsWith ops fuel recur ps with
      | some c, some cs =>
          let c := match p with
            | .vararg _ n => PType.vararg c n
            | _ => c
          some (c :: cs)
      | _, _ => none

def pTypejoinUnionTupleWith (ops : PTypeOps) (fuel : Nat) (recur : PType → PType) :
    PType → PType
  | .data "Tuple" wrapper ps super =>
      match pTypejoinUnionParamsWith ops fuel recur ps with
      | some cs => .data "Tuple" wrapper cs super
      | none => .any
  | _ => .any

def pPromoteTypejoinUnion (ops : PTypeOps) : Nat → PType → PType
  | 0, _ => .any
  | _, .bottom => .bottom
  | _, .unionAll .. => .any
  | fuel + 1, .union a b =>
      pPromoteTypejoin ops (pPromoteTypejoinUnion ops fuel a)
        (pPromoteTypejoinUnion ops fuel b)
  | fuel + 1, t@(.data "Tuple" _ _ _) =>
      pTypejoinUnionTupleWith ops fuel (pPromoteTypejoinUnion ops fuel) t
  | _, .data n w ps s => .data n w ps s
  | _, .typeEq t => .typeEq t
  | _, _ => .any

def pTypejoinUnionTuple (ops : PTypeOps) (fuel : Nat) (t : PType) : PType :=
  pTypejoinUnionTupleWith ops fuel (pPromoteTypejoinUnion ops fuel) t

def pTailjoin (ops : PTypeOps) (ps : List PType) (i : Nat) : PType :=
  if ps.length < i then pUnwrapVa (ps.getLastD .bottom)
  else (ps.drop (i - 1)).foldl (pTypejoin ops 64) .bottom

inductive Ty where
  | bottom
  | any
  | atom (name : Nat) (ancestors : List Nat)
  | union (left right : Ty)
  | typeVar (upper : Ty)
  | unionAll (body : Ty)
  | typeEq (parameter : Ty)
  | tuple (parameters : List Ty)
  deriving BEq, Repr

def subtype : Ty → Ty → Bool
  | _, .any => true
  | .bottom, _ => true
  | a, b => a == b

def atomJoin (an : Nat) (aa : List Nat) (bn : Nat) (ba : List Nat) : Ty :=
  if an = bn then .atom an aa
  else match (an :: aa).find? (fun n => (bn :: ba).contains n) with
    | some n => .atom n []
    | none => .any

/-- Finite source model of `typejoin`; it follows the source branch order for
TypeVar, identity, subtyping, UnionAll, Union, Type equality kinds, tuples, and
ordinary datatype ancestry. Fuel represents Julia's finite type graph;
`base/promotion.jl:20-160`. -/
def typejoin : Nat → Ty → Ty → Ty
  | 0, _, _ => .any
  | fuel + 1, a, b =>
      match a, b with
      | .typeVar u, b => typejoin fuel u b
      | a, .typeVar u => typejoin fuel a u
      | a, b =>
        if a == b then a
        else if subtype a b then b
        else if subtype b a then a
        else match a, b with
          | .unionAll body, b => .unionAll (typejoin fuel body b)
          | a, .unionAll body => .unionAll (typejoin fuel a body)
          | .union x y, b => typejoin fuel (typejoin fuel x y) b
          | a, .union x y => typejoin fuel a (typejoin fuel x y)
          | .typeEq x, b => typejoin fuel x b
          | a, .typeEq y => typejoin fuel a y
          | .tuple xs, .tuple ys => .tuple (List.zipWith (typejoin fuel) xs ys)
          | .tuple _, _ | _, .tuple _ => .any
          | .atom an aa, .atom bn ba => atomJoin an aa bn ba
          | _, _ => .any

def typesplit : Ty → Ty → Ty
  | a, b => if subtype a b then .bottom else match a with
    | .union x y => .union (typesplit x b) (typesplit y b)
    | _ => a

def promoteTypejoin (a b : Ty) : Ty := .union a (.union b (typejoin 64 a b))

/-- `_promote_typesubtract`; `base/promotion.jl:202-207`. -/
def promoteTypesubtract (a : Ty) : Ty :=
  match a with
  | .any => .any
  | .union x y =>
      let withoutBottom := typesplit (.union x y) .bottom
      withoutBottom
  | _ => a

/-- Union normalization used by `promote_typejoin_union` and tuple elements;
`base/promotion.jl:209-253`. -/
def promoteTypejoinUnion : Nat → Ty → Ty
  | 0, _ => .any
  | _fuel + 1, .bottom => .bottom
  | _fuel + 1, .unionAll _ => .any
  | fuel + 1, .union a b => promoteTypejoin (promoteTypejoinUnion fuel a) (promoteTypejoinUnion fuel b)
  | fuel + 1, .tuple xs => .tuple (xs.map (promoteTypejoinUnion fuel))
  | _, t => t

/-- `full_va_len` and `tailjoin`; a `none` final length is an open Vararg;
`base/promotion.jl:256-280`. -/
def fullVaLen (params : List (Ty × Option Nat)) : Nat × Bool :=
  match params.getLast? with
  | none => (0, true)
  | some (_, some n) => (params.length + n - 1, true)
  | some (_, none) => (params.length, false)

def tailjoin (params : List Ty) (i : Nat) : Ty :=
  if params.length < i then params.getLastD .bottom
  else (params.drop (i - 1)).foldl (typejoin 64) .bottom

def promoteType : Nat → (Ty → Ty → Ty) → Ty → Ty → Ty
  | 0, _, _, _ => .any
  | fuel + 1, rule, a, b =>
      if a == .bottom then b
      else if b == .bottom then a
      else if a == b then a
      else
        let r1 := rule a b
        let r2 := rule b a
        if r1 == .bottom && r2 == .bottom then typejoin fuel a b
        else promoteType fuel rule r1 r2

def promoteType0 : Ty := .bottom
def promoteType1 (t : Ty) : Ty := t
def promoteType3 (rule : Ty → Ty → Ty) (t s u : Ty) : Ty :=
  promoteType 64 rule (promoteType 64 rule t s) u
def promoteTypeMany (rule : Ty → Ty → Ty) (t s u : Ty) (ts : List Ty) : Ty :=
  ts.foldl (promoteType 64 rule) (promoteType3 rule t s u)
def promoteRuleDefault (_ _ : Ty) : Ty := .bottom
def promoteRuleBottomLeft (_ : Ty) : Ty := .bottom
def promoteRuleBottomRight (t : Ty) : Ty := t
def promoteResult (rule : Ty → Ty → Ty) (t s r1 r2 : Ty) : Ty :=
  if r1 == .bottom && r2 == .bottom then typejoin 64 t s
  else promoteType 64 rule r1 r2

/-- Value promotion; `base/promotion.jl:397-441`. -/
def promote2 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y : α) : α × α :=
  let t := promoteType 64 rule (typeOf x) (typeOf y)
  (convert t x, convert t y)

def promote3 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y z : α) : α × α × α :=
  let t := promoteType 64 rule (promoteType 64 rule (typeOf x) (typeOf y)) (typeOf z)
  (convert t x, convert t y, convert t z)

def promoteMany (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (xs : List α) : List α :=
  let t := (xs.map typeOf).foldl (promoteType 64 rule) .bottom
  xs.map (convert t)

def promoteTypeof1 (typeOf : α → Ty) (x : α) : Ty := typeOf x
def promoteTypeof2 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y : α) : Ty :=
  promoteType 64 rule (typeOf x) (typeOf y)
def promoteTypeof3 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y z : α) : Ty :=
  promoteType3 rule (typeOf x) (typeOf y) (typeOf z)
def promoteTypeofMany (typeOf : α → Ty) (rule : Ty → Ty → Ty)
    (x y z : α) (xs : List α) : Ty :=
  (xs.map typeOf).foldl (promoteType 64 rule) (promoteTypeof3 typeOf rule x y z)

def promote0 : List α := []
def promote1 (x : α) : List α := [x]
def promoteSame (x y : α) (zs : List α) : List α := x :: y :: zs

/-- Circular-promotion check; `base/promotion.jl:443-452`. -/
def notSameType (sameType : List α → List α → Bool) (before after : List α) : Jl Unit :=
  if sameType before after then .error (.argumentError "promotion failed") else .ok ()

/-- Mixed arithmetic forwards after promotion; `base/promotion.jl:454-527`. -/
def promotedBinary (promote : α → α → α × α) (op : α → α → β) (x y : α) : β :=
  let p := promote x y
  op p.1 p.2

def promotedTernary (promote : α → α → α → α × α × α)
    (op : α → α → α → β) (x y z : α) : β :=
  let p := promote x y z
  op p.1 p.2.1 p.2.2

/-- `muladd` preserves strong zero before same-type dispatch;
`base/promotion.jl:510-514`. -/
def promotedMuladd (promote : α → α → α → α × α × α)
    (muladd : α → α → α → α) (isFalse : α → Bool) (a b c : α) : α :=
  let p := promote a b c
  if isFalse a || isFalse b then p.2.2 else muladd p.1 p.2.1 p.2.2

/-- `TupleOrBottom`; `base/promotion.jl:529-532`. -/
def tupleOrBottom (ts : List Ty) : Ty := if ts.contains .bottom then .bottom else .tuple ts

/-- `promote_op`; inference is supplied as the primitive `_return_type`;
`base/promotion.jl:641-645`. -/
def promoteOp (returnType : (α → β) → Ty → Ty) (f : α → β) (ts : List Ty) : Ty :=
  let arg := tupleOrBottom ts
  if arg == .bottom then .bottom else returnType f arg

/-- Same-type catch-all arithmetic; `base/promotion.jl:650-680`. -/
def noOp (_name : String) : Jl α := .error (.methodError "numeric operation")
def fallbackMuladd (mul add : α → α → α) (x y z : α) : α := add (mul x y) z
def fallbackEq (identical : α → α → Bool) (x y : α) : Bool := identical x y
def fallbackLe (eq lt : α → α → Bool) (x y : α) : Bool := eq x y || lt x y
def fallbackMax (lt : α → α → Bool) (x y : α) : α := if lt y x then x else y
def fallbackMin (lt : α → α → Bool) (x y : α) : α := if lt y x then y else x
def fallbackMinmax (lt : α → α → Bool) (x y : α) : α × α :=
  if lt y x then (y, x) else (x, y)
def fallbackUnary (x : α) : α := x

end PromotionModel

end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Promotion

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

abbrev PT := PromotionModel.PType
abbrev POps := PromotionModel.PTypeOps
abbrev Ty := PromotionModel.Ty

def m20 : PT := PromotionModel.pTypejoin0
def m21 (t : PT) := PromotionModel.pTypejoin1 t
def m22 (o : POps) a b c := PromotionModel.pTypejoin3 o a b c
def m23 (o : POps) a b c ts := PromotionModel.pTypejoinMany o a b c ts
def m25 (a : PT) name := PromotionModel.pHasAncestorName a name
def m37 (o : POps) a b := PromotionModel.pTypejoin o 64 a b
def m166 (o : POps) a b := PromotionModel.pTypesplit o a b
def m198 (o : POps) a b := PromotionModel.pPromoteTypejoin o a b
def m202 (o : POps) nothing missing a := PromotionModel.pPromoteTypesubtract o nothing missing a
def m209 (o : POps) t := PromotionModel.pPromoteTypejoinUnion o 64 t
def m226 (o : POps) t := PromotionModel.pTypejoinUnionTuple o 64 t
def m256 ps := PromotionModel.pFullVaLen ps
def m270 (o : POps) ps i := PromotionModel.pTailjoin o ps i
def m326 : Ty := PromotionModel.promoteType0
def m327 (t : Ty) := PromotionModel.promoteType1 t
def m328 rule t s u := PromotionModel.promoteType3 rule t s u
def m329 rule t s u ts := PromotionModel.promoteTypeMany rule t s u ts
def m331 : Ty := .bottom
def m332 (t : Ty) := t
def m333 := m332
def m334 := m332
def m336 rule t s := PromotionModel.promoteType 64 rule t s
def m355 (_ _ : Ty) : Ty := .bottom
def m358 (_ : List Ty) : Ty := .bottom
def m359 := m358
def m360 (t : Ty) (_ : List Ty) := t
def m361 := m360
def m363 (rule : Ty → Ty → Ty) (_t _s a b : Ty) := PromotionModel.promoteType 64 rule a b
def m366 (_rule : Ty → Ty → Ty) (t s : Ty) := PromotionModel.typejoin 64 t s
def m397 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y : α) := PromotionModel.promote2 typeOf convert rule x y
def m402 (typeOf : α → Ty) (x : α) := PromotionModel.promoteTypeof1 typeOf x
def m403 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y : α) :=
  PromotionModel.promoteTypeof2 typeOf rule x y
def m404 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y z : α) :=
  PromotionModel.promoteTypeof3 typeOf rule x y z
def m405 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y z : α) (xs : List α) :=
  PromotionModel.promoteTypeofMany typeOf rule x y z xs
def m406 := @PromotionModel.promote3
def m411 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y : α) (zs : List α) := PromotionModel.promoteMany typeOf convert rule (x :: y :: zs)
def m420 : List α := []
def m421 (x : α) := [x]
def m423 (promote : α → α → α × α) (same : (α × α) → (α × α) → Bool)
    (x y : α) : Jl (α × α) :=
  let p := promote x y
  if same (x, y) p then .error (.argumentError "promotion failed") else .ok p
def m429 (promote : α → α → α → α × α × α)
    (same : (α × α × α) → (α × α × α) → Bool)
    (x y z : α) : Jl (α × α × α) :=
  let p := promote x y z
  if same (x, y, z) p then .error (.argumentError "promotion failed") else .ok p
def m435 (promote : List α → List α) (same : List α → List α → Bool)
    (xs : List α) : Jl (List α) :=
  let p := promote xs
  if same xs p then .error (.argumentError "promotion failed") else .ok p
def m441 (x y : α) (zs : List α) := PromotionModel.promoteSame x y zs
def m443 (_x _y : α) : Jl Unit := .error (.argumentError "promotion failed")
def m445 (_x : α) (_y : β) : Unit := ()
def m447 (renderTypes : α → String) (x : α) : Jl β := .error (.argumentError (renderTypes x))
def forward2 (promote : α → α → α × α) (op : α → α → β) x y :=
  let p := promote x y
  op p.1 p.2
def m454 := @forward2
def m455 := @forward2
def m456 := @forward2
def m457 := @forward2
def m459 := @forward2
def m460 := @forward2
def m461 := @forward2
def m507 := @forward2
def m516 := @forward2
def m517 := @forward2
def m518 := @forward2
def m520 := @forward2
def m521 := @forward2
def m522 := @forward2
def m523 := @forward2
def m525 := @forward2
def m526 := @forward2
def m527 := @forward2

def m509 (promote : α → α → α → α × α × α) (op : α → α → α → β)
    (x y z : α) := PromotionModel.promotedTernary promote op x y z
def m510 (promote : α → α → α → α × α × α) (muladd : α → α → α → α)
    (isFalse : α → Bool) (a b c : α) :=
  PromotionModel.promotedMuladd promote muladd isFalse a b c
def m529 (ts : List Ty) := PromotionModel.tupleOrBottom ts
def m641 (returnType : (α → β) → Ty → Ty) (f : α → β) (ts : List Ty) :=
  PromotionModel.promoteOp returnType f ts
def noOp (name : String) : Jl α := .error (.methodError name)
def m650 := @noOp
def m651 := @noOp
def m652 := @noOp
def m653 := @noOp
def m654 := @noOp
def m655 := @noOp
def m657 := @noOp
def m661 := @noOp
def m662 := @noOp
def m663 := @noOp
def m666 := @noOp
def m669 := @noOp
def m670 := @noOp
def m680 := @noOp
def m658 (mul add : α → α → α) x y z := add (mul x y) z
def m659 := @m658
def m665 (identical : α → α → Bool) x y := identical x y
def m667 (eq lt : α → α → Bool) x y := eq x y || lt x y
def m672 (x : α) := x
def m673 := @m672
def m674 (x : α) := (x, x)
def m676 (lt : α → α → Bool) x y := if lt y x then x else y
def m677 (lt : α → α → Bool) x y := if lt y x then y else x
def m678 (lt : α → α → Bool) x y := if lt y x then (y, x) else (x, y)

end JuliaLean.NumbersCov.Rows.Promotion

namespace JuliaLean.HashOps

inductive FmaResult (α : Type) where
  | ok (value : α)
  | noOperation
  deriving DecidableEq, Repr

/-- `fma(::T,::T,::T)` catch-all (`base/promotion.jl:657`) and its Integer
specialization at line 658. -/
def fmaNumberFallback (_ _ _ : α) : FmaResult α := .noOperation
def fmaIntegerFallback (o : FallbackOps α) (x y z : α) : FmaResult α :=
  .ok (o.add (o.mul x y) z)

end JuliaLean.HashOps
namespace JuliaLean.Promotion

/-- The modelled primitive number types. -/
inductive NumTy where
  | bool
  | int (t : IntTy)
  | flt (T : FTy)
  deriving DecidableEq, Repr

def FTy.width : FTy → Nat
  | .f16 => 16 | .f32 => 32 | .f64 => 64

/-- `promote_rule(T, S)`; `none` is `Bottom` (`base/promotion.jl:355`). Rules:
`base/bool.jl:6`; integers `base/int.jl:809-822`; float/integer `base/float.jl:243-263`;
floats `base/float.jl:477-479`. -/
def promoteRule : NumTy → NumTy → Option NumTy
  | .bool, s => if s = .bool then none else some s
  | .int t, .int s =>
    if t.bits > s.bits then some (.int t)
    else if t.bits = s.bits ∧ !t.signed ∧ s.signed then some (.int t)
    else none
  | .flt T, .int _ => some (.flt T)
  | .flt T, .bool => some (.flt T)
  | .flt T, .flt S => if T.width > S.width then some (.flt T) else none
  | _, _ => none

/-- `promote_type(T, S)`; `base/promotion.jl:332-344` with `promote_result`
(`base/promotion.jl:363-366`). `none` stands for a non-concrete `typejoin`. -/
def promoteType (t s : NumTy) : Option NumTy :=
  if t = s then some t
  else match promoteRule t s, promoteRule s t with
    | some a, none => some a
    | none, some b => some b
    | some a, some b => if a = b then some a else none
    | none, none => none

end JuliaLean.Promotion

namespace JuliaLean.IntArith.Division

/-- `base/int.jl:809-822`, `base/promotion.jl:397-401,423-428`: checked value promotion. -/
def promote (x y : Value) : Jl (Value × Value) := do
  let t := IntTy.promote x.ty y.ty
  let a ← JInt.convert (t.name) t x.int.val
  let b ← JInt.convert (t.name) t y.int.val
  pure (pack a, pack b)

/-- Same-signedness remainder after checked promotion, `base/promotion.jl:520`,
`base/int.jl:355-358,1085-1089`. -/
def promotedRem (x y : Value) : Jl Value := do
  let t := IntTy.promote x.ty y.ty
  let a ← JInt.convert (t.name) t x.int.val
  let b ← JInt.convert (t.name) t y.int.val
  pure (pack (← JInt.remInt a b))

end JuliaLean.IntArith.Division
