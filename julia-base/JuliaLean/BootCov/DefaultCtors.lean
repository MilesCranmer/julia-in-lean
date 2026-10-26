import JuliaLean.BootCov.Types

/-!
Default-constructor generation of `base/essentials.jl` (master `bbfa0ce4150`, lines
1290-1504): `_fieldtypes_constrain_typevars`, `_defaultctor_typeinfo` and `_defaultctors`.

Arrays `Array{Any,1}(undef, k)` are lists of `k` slots, `none` for `#undef`; `@inbounds a[i] = x`
is `setAt a i x`; splatting an array into a call (`Expr(head, a...)`, `Core.svec(a...)`) is
`splat a`, which throws `UndefRefError` at an undefined slot. A counted `while` loop over
`fts[i]` (`i = 1, ..., n`) is a recursion over the list of remaining field types, carrying
`i`. The `jl_method_def` calls are recorded as the returned `MethodDef`s, in call order; each
holds the argument types and type variables of the `argdata` svec and the `:lambda`
expression handed to `jl_lower`.
-/

namespace JuliaLean.BootCov.DefaultCtors

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.Types

/-- The type `Any`. -/
def anyTy : JType := .dt "Any" true []

/-- `ft === Any`. -/
def isAnyTy : JType → Bool
  | .dt "Any" _ [] => true
  | _ => false

/-- The typeassert `x::TypeVar`. -/
def asTypeVar : JType → R JType
  | t@(.tvar _ _ _ _) => .ok t
  | _ => .error (.typeError "typeassert")

/-- `tv.ub` of a `TypeVar`. -/
def tvUb : JType → JType
  | .tvar _ _ _ ub => ub
  | t => t

/-- `tv2 === tv` for two `TypeVar`s: object identity. -/
def sameVar : JType → JType → Bool
  | .tvar a _ _ _, .tvar b _ _ _ => a == b
  | _, _ => false

/-! ## `_fieldtypes_constrain_typevars(tvars, fts)`, lines 1292-1329 -/

/-- The first inner loop (lines 1300-1307): `j = 1, ..., n`; `constrained = true; break`
at the first `has_typevar(fts[j], tv)`. -/
def fieldLoop (tv : JType) : List JType → Bool
  | [] => false
  | ft :: fts => if hasTypevar ft tv then true else fieldLoop tv fts

/-- The second inner loop (lines 1309-1322), run only when the first found nothing:
`tv2 = tvars[j]::TypeVar` for `j = i + 1, ..., nparams`; `true` at the first
`has_typevar(tv2.ub, tv)`, `false` at the first `tv2 === tv`. -/
def ubLoop (tv : JType) : List JType → R Bool
  | [] => .ok false
  | t :: ts => do
    let tv2 ← asTypeVar t
    if hasTypevar (tvUb tv2) tv then .ok true
    else if sameVar tv2 tv then .ok false
    else ubLoop tv ts

/-- The outer loop (lines 1296-1327) for `i = nparams, ..., 1`; `tvars.getD i` is
`tvars[i + 1]` and `tvars.drop (i + 1)` lists `tvars[j]` for `j = i + 2, ..., nparams`. -/
def outerLoop (tvars fts : List JType) : Nat → R Bool
  | 0 => .ok true
  | i + 1 => do
    let tv ← asTypeVar (tvars.getD i .bottom)
    let constrained ← if fieldLoop tv fts then pure true else ubLoop tv (tvars.drop (i + 1))
    if constrained then outerLoop tvars fts i else .ok false

def fieldtypesConstrainTypevars (tvars fts : List JType) : R Bool :=
  outerLoop tvars fts tvars.length

/-! ## `_defaultctor_typeinfo(ty)`, lines 1332-1350 -/

/-- `while isa(ua, UnionAll); nparams += 1; ua = ua.body; end`. -/
def peelLoop : Nat → JType → Nat × JType
  | n, .unionAll _ b => peelLoop (n + 1) b
  | n, t => (n, t)

/-- `tvars[i] = (ua::UnionAll).var; ua = (ua::UnionAll).body` for `i = 1, ..., nparams`. -/
def varsLoop : Nat → JType → R (List JType)
  | 0, _ => .ok []
  | k + 1, .unionAll v b => do
    let vs ← varsLoop k b
    pure (v :: vs)
  | _ + 1, _ => .error (.typeError "typeassert")

def isDataType : JType → Bool
  | .dt _ _ _ => true
  | _ => false

/-- `_defaultctor_typeinfo(ty)`; `getFieldtypes` is `jl_get_fieldtypes`. -/
def defaultctorTypeinfo (getFieldtypes : JType → List JType) (ty : JType) :
    R (JType × List JType × List JType) :=
  let (nparams, ua) := peelLoop 0 ty
  if isDataType ua then do
    let tvars ← varsLoop nparams ty
    pure (ua, tvars, getFieldtypes ua)
  else .error (.typeError "typeassert")

/-! ## `_defaultctors(ty, functionloc)`, lines 1355-1504 -/

/-- `Core.Argument(i)`. -/
def argument (i : Nat) : JVal := .obj "Argument" [some (.int i)]
/-- `Expr(:ssavalue, k)`. -/
def ssa (k : Nat) : JVal := .expr "ssavalue" [.int k]

/-- `Array{Any,1}(Core.undef, k)`. -/
def undefArr (k : Nat) : List (Option JVal) := List.replicate k none
/-- `@inbounds a[i] = x` (one-based). -/
def setAt (a : List (Option JVal)) (i : Nat) (x : JVal) : List (Option JVal) :=
  a.set (i - 1) (some x)
/-- The bounds-checked `a[i] = x`. -/
def setChecked (a : List (Option JVal)) (i : Nat) (x : JVal) : R (List (Option JVal)) :=
  if 1 ≤ i ∧ i ≤ a.length then .ok (setAt a i x) else .error .bounds
/-- Splatting an array: every slot is read, an undefined one throws `UndefRefError`. -/
def splat : List (Option JVal) → R (List JVal)
  | [] => .ok []
  | none :: _ => .error .undefRef
  | some x :: xs => do
    let ys ← splat xs
    pure (x :: ys)
/-- The typeassert `names[i]::Symbol`. -/
def asSymbol : JVal → R JVal
  | v@(.sym _) => .ok v
  | _ => .error (.typeError "typeassert")

/-- One `jl_method_def(svec(atypes, tvars, functionloc), C_NULL, jl_lower(lambda, ...))`. -/
structure MethodDef where
  atypes : List JVal
  tvars : List JVal
  lambda : JVal

/-- Lines 1376-1384: `argnames[i + 1] = names[i]::Symbol` and the count of `Any` fields,
for `i = 1, ..., n` (`n = length(fts)`). -/
def argnamesLoop : Nat → List JVal → List JType → List (Option JVal) → Nat →
    R (List (Option JVal) × Nat)
  | _, _, [], a, nany => .ok (a, nany)
  | i, nm :: nms, ft :: fts, a, nany => do
    let s ← asSymbol nm
    let a := setAt a (i + 1) s
    let nany := if isAnyTy ft then nany + 1 else nany
    argnamesLoop (i + 1) nms fts a nany
  | _, [], _ :: _, _, _ => .error .bounds

/-- Lines 1394-1397: `curly_args[i + 1] = Expr(:static_parameter, i)`, `i = 1, ..., nparams`. -/
def curlyLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => curlyLoop (i + 1) k (setAt a (i + 1) (.expr "static_parameter" [.int i]))

/-- Lines 1405-1408: `new_args[i + 1] = Core.Argument(i + 1)`, `i = 1, ..., n`. -/
def newArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => newArgsLoop (i + 1) k (setAt a (i + 1) (argument (i + 1)))

/-- Lines 1418-1421: `atypes_arr[i + 1] = fts[i]`. -/
def atypesLoop : Nat → List JType → List (Option JVal) → List (Option JVal)
  | _, [], a => a
  | i, ft :: fts, a => atypesLoop (i + 1) fts (setAt a (i + 1) (.ty ft))

/-- Lines 1429-1437: `all_any` is false at the first `fts[i] !== Any`. -/
def allAnyLoop : List JType → Bool
  | [] => true
  | ft :: fts => if !isAnyTy ft then false else allAnyLoop fts

/-- The `fieldtype(self, i)` statement of field `i`, line 1462. -/
def ftStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa bidx, .expr "call" [.globalRef "Core" "fieldtype", argument 1, .int i]]
/-- The `isa(arg, ft) ? arg : convert(ft, arg)` statement of field `i`, lines 1465-1469. -/
def cnvtStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa (bidx + 1), .expr "if"
    [.expr "call" [.globalRef "Core" "isa", argument (i + 1), ssa bidx], argument (i + 1),
     .expr "call" [.globalRef "Base" "convert", ssa bidx, argument (i + 1)]]]

/-- Lines 1448-1475: for `i = 1, ..., n`, an `Any` field passes `Core.Argument(i + 1)`;
any other field gets the two statements at `bidx` and `bidx + 1` and passes the second's
SSA value; `bidx += 2`. -/
def innerLoop : Nat → Nat → List JType → List (Option JVal) → List (Option JVal) →
    List (Option JVal) × List (Option JVal)
  | _, _, [], body, na => (body, na)
  | i, bidx, ft :: fts, body, na =>
    if isAnyTy ft then innerLoop (i + 1) bidx fts body (setAt na i (argument (i + 1)))
    else
      let body := setAt body bidx (ftStmt i bidx)
      let body := setAt body (bidx + 1) (cnvtStmt i bidx)
      innerLoop (i + 1) (bidx + 2) fts body (setAt na i (ssa (bidx + 1)))

/-- Lines 1486-1491: `typedt = UnionAll(tvars[i], typedt)` for `i = nparams, ..., 1`. -/
def wrapLoop (tvars : List JType) : Nat → JType → R JType
  | 0, t => .ok t
  | i + 1, t => do
    let t ← unionAllCtor (tvars.getD i .bottom) t
    wrapLoop tvars i t

/-- Lines 1494-1497: `inner_atypes_arr[i + 1] = Any`. -/
def anyArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => anyArgsLoop (i + 1) k (setAt a (i + 1) (.ty anyTy))

/-- `UInt(functionloc.line)` (line 1366): `InexactError` for a negative line. -/
def srcLine : JVal → R Nat
  | .lineNode l _ => if l < 0 then .error (.inexact "convert" "UInt64") else .ok l.toNat
  | _ => .error (.typeError "getfield")

/-- The outer constructor (lines 1386-1427) `T(x::FT1, ...) = new{A,...}(x, ...)`. -/
def outerCtor (ty : JType) (tvars fts : List JType) (argnames : JVal) (functionloc : JVal) :
    R MethodDef := do
  let nparams := tvars.length
  let n := fts.length
  let newTarget ← if nparams != 0 then do
      let curlyArgs := curlyLoop 1 nparams (setAt (undefArr (nparams + 1)) 1 (.ty ty))
      let cargs ← splat curlyArgs
      pure (JVal.expr "curly" cargs)
    else pure (argument 1)
  let newArgs := newArgsLoop 1 n (setAt (undefArr (n + 1)) 1 newTarget)
  let nargs ← splat newArgs
  let lambda := JVal.expr "lambda" [argnames,
    .expr "block" [functionloc, .expr "return" [.expr "new" nargs]]]
  let atypesArr := atypesLoop 1 fts (setAt (undefArr (n + 1)) 1 (.ty (typeKind ty)))
  let outerAtypes ← splat atypesArr
  pure ⟨outerAtypes, tvars.map .ty, lambda⟩

/-- The inner constructor (lines 1442-1502) `(::Type{T{A,...}})(x, ...)` with converts. -/
def innerCtor (dt : JType) (tvars fts : List JType) (nany : Nat) (argnames : JVal)
    (functionloc : JVal) : R MethodDef := do
  let nparams := tvars.length
  let n := fts.length
  let nstmts := (n - nany) + (n - nany) + 1
  let (bodyArgs, newArgs) := innerLoop 1 1 fts (undefArr nstmts) (undefArr n)
  let na ← splat newArgs
  let bodyArgs ← setChecked bodyArgs nstmts (.expr "return" [.expr "new" (argument 1 :: na)])
  let stmts ← splat bodyArgs
  let lambda := JVal.expr "lambda" [argnames, .expr "block" (functionloc :: stmts)]
  let typedt ← wrapLoop tvars nparams (typeKind dt)
  let innerAtypesArr := anyArgsLoop 1 n (setAt (undefArr (n + 1)) 1 (.ty typedt))
  let innerAtypes ← splat innerAtypesArr
  pure ⟨innerAtypes, [], lambda⟩

/-- `_defaultctors(ty, functionloc)`: `getFieldtypes` is `jl_get_fieldtypes` and `getNames`
reads `dt.name.names`. The result lists the methods defined, in order. -/
def defaultctors (getFieldtypes : JType → List JType) (getNames : JType → List JVal)
    (ty : JType) (functionloc : JVal) : R (List MethodDef) := do
  let (dt, tvars, fts) ← defaultctorTypeinfo getFieldtypes ty
  let nparams := tvars.length
  let n := fts.length
  let names := getNames dt
  let _ ← srcLine functionloc
  let self := JVal.sym "#ctor-self#"
  let (argnames, nany) ← argnamesLoop 1 names fts (setAt (undefArr (n + 1)) 1 self) 0
  let argnamesV := JVal.obj "Array{Any,1}" argnames
  let constrained ← fieldtypesConstrainTypevars tvars fts
  if constrained then do
    let outer ← outerCtor ty tvars fts argnamesV functionloc
    if nparams = 0 ∧ allAnyLoop fts then return [outer]
    let inner ← innerCtor dt tvars fts nany argnamesV functionloc
    pure [outer, inner]
  else do
    let inner ← innerCtor dt tvars fts nany argnamesV functionloc
    pure [inner]

/-- `length(t::AbstractArray) = (@inline; prod(size(t)))`, `base/essentials.jl:13`:
`prod` of the size tuple multiplies left to right with `Int` wrapping (`prod(()) = 1`). -/
def lengthAbstract (size : List JInt64) : JInt64 :=
  match size with
  | [] => JInt.lit .i64 1
  | d :: ds => ds.foldl (· * ·) d

end JuliaLean.BootCov.DefaultCtors
