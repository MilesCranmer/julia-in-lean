import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.bool
import JuliaLean.base.float

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
def typejoinPair (ops : PTypeOps) (join : PType → PType → Option PType)
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
  unfold typejoinPair
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
def equalNumber (promote : α → α → m (β × β)) (equal : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  equal px py

/--
Julia source: base/promotion.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::Real, y::Real)     = (< )(promote(x,y)...)
```
-/
def lessNumber (promote : α → α → m (β × β)) (less : β → β → m γ)
    (x y : α) : m γ := do
  let (px, py) ← promote x y
  less px py

/--
Julia source: base/promotion.jl:518-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Real, y::Real)     = (<=)(promote(x,y)...)
```
-/
def lessEqualNumber (promote : α → α → m (β × β)) (lessEqual : β → β → m γ)
    (x y : α) : m γ := do
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
def mod1Number (promote : α → α → m (β × β)) (mod1 : β → β → m γ)
    (x y : α) : m γ := do
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

end JuliaLean.base.promotion
