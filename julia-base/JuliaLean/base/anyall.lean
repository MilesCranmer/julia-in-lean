import JuliaLean.base.operators
import JuliaLean.base.generator
import JuliaLean.base.reduce

/-!
# Model of `base/anyall.jl`

Predicate results are `PredicateValue.bool` or `PredicateValue.missing`; `other` models a value
that raises Julia's boolean-context `TypeError`. Iterator interfaces supply the finite sequence
visited by a `for` loop. Tuple methods use lists of fields, including `TupleValue` for heterogeneous
tuples. Callback errors remain observable, so the loop models short-circuiting.
-/

namespace JuliaLean.base.anyall

inductive PredicateValue where
  | bool (value : Bool)
  | missing
  | other
  deriving Repr, DecidableEq

inductive AnyAllError (ε : Type) where
  | predicate (error : ε)
  | typeError

inductive Colon where
  | colon

abbrev TupleValue := Σ α : Type, α

/--
Julia source: base/anyall.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
any(itr) = any(identity, itr)
```
-/
def anyIdentity {ε I : Type}
    (anyCall : (PredicateValue → Except ε PredicateValue) → I →
      Except (AnyAllError ε) (Option Bool))
    (itr : I) : Except (AnyAllError ε) (Option Bool) :=
  anyCall (fun x => .ok (JuliaLean.base.operators.identity x)) itr

/--
Julia source: base/anyall.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
all(itr) = all(identity, itr)
```
-/
def allIdentity {ε I : Type}
    (allCall : (PredicateValue → Except ε PredicateValue) → I →
      Except (AnyAllError ε) (Option Bool))
    (itr : I) : Except (AnyAllError ε) (Option Bool) :=
  allCall (fun x => .ok (JuliaLean.base.operators.identity x)) itr

/--
Julia source: base/anyall.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
any(f, itr) = _any(f, itr, :)
```
-/
def anyPredicate {ε I α : Type}
    (anyImpl : (I → List α) → (α → Except ε PredicateValue) → I → Colon →
      Except (AnyAllError ε) (Option Bool))
    (items : I → List α) (f : α → Except ε PredicateValue) (itr : I) :
    Except (AnyAllError ε) (Option Bool) :=
  anyImpl items f itr .colon

/--
Julia source: base/anyall.jl:120-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function _any(f, itr::$ItrT, ::Colon)
        $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
        anymissing = false
        for x in itr
            v = f(x)
            if ismissing(v)
                anymissing = true
            else
                v && return true
            end
        end
        return anymissing ? missing : false
    end
```
-/
def anyTupleLoop {ε α : Type} (f : α → Except ε PredicateValue) (itr : List α)
    (_colon : Colon) : Except (AnyAllError ε) (Option Bool) :=
  let rec loop (anymissing : Bool) : List α → Except (AnyAllError ε) (Option Bool)
    | [] => .ok (if anymissing then none else some false)
    | x :: rest =>
        match f x with
        | .error e => .error (.predicate e)
        | .ok .missing => loop true rest
        | .ok (.bool true) => .ok (some true)
        | .ok (.bool false) => loop anymissing rest
        | .ok .other => .error .typeError
  loop false itr

/--
Julia source: base/anyall.jl:120-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function _any(f, itr::$ItrT, ::Colon)
        $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
        anymissing = false
        for x in itr
            v = f(x)
            if ismissing(v)
                anymissing = true
            else
                v && return true
            end
        end
        return anymissing ? missing : false
    end
```
-/
def anyAny {ε I α : Type} (items : I → List α) (f : α → Except ε PredicateValue)
    (itr : I) (_colon : Colon) : Except (AnyAllError ε) (Option Bool) :=
  let rec loop (anymissing : Bool) : List α → Except (AnyAllError ε) (Option Bool)
    | [] => .ok (if anymissing then none else some false)
    | x :: rest =>
        match f x with
        | .error e => .error (.predicate e)
        | .ok .missing => loop true rest
        | .ok (.bool true) => .ok (some true)
        | .ok (.bool false) => loop anymissing rest
        | .ok .other => .error .typeError
  loop false (items itr)

/-- anyall.jl:120-132 `_any(f, itr, :)` with `for x in itr` lowered to the
collection's own `iterate` (`iterate(itr)`, then `iterate(itr, state)`): a `missing` value sets
`anymissing` and iteration continues (anyall.jl:125-127), `v && return true` stops at the first
`true` without iterating further, and once `iterate` returns `nothing` the result is `missing`
if `anymissing`, else `false`. An exception from `iterate` or `f` propagates; an `iterate`
that never returns `nothing` gives `none`. -/
def anyIterate {E A St : Type} (iterate : Option St → ExceptT E Option (Option (A × St)))
    (f : A → ExceptT E Option operators.Truth) (anymissing : Bool) (state : Option St) :
    ExceptT E Option operators.Truth := do
  match ← iterate state with
  | none => pure (if anymissing then .missing else .false)
  | some (x, next) =>
      match ← f x with
      | .missing => anyIterate iterate f true (some next)
      | .true => pure .true
      | .false => anyIterate iterate f anymissing (some next)
partial_fixpoint

/--
Julia source: base/anyall.jl:137-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _any(::typeof(identity), itr::Tuple{Vararg{Bool}}, ::Colon)
    @_terminates_locally_meta
    r = false
    for i in eachindex(itr)
        # Avoid bounds checking to help vectorization. Use `getfield` directly,
        # instead of `@inbounds itr[i]`, for better effects.
        v = getfield(itr, i, false)
        r |= v
    end
    r
end
```
-/
def anyBoolTuple (itr : List Bool) (_colon : Colon) : Bool :=
  itr.foldl (fun r value => r || value) false

/--
Julia source: base/anyall.jl:152-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function any(f, itr::Tuple)
    if itr isa NTuple || length(itr) > 32
        return _any(f, itr, :)
    end
    _any_tuple(f, false, itr...)
end
```
-/
def anyTupleMethod {ε α : Type}
    (anyImpl : (α → Except ε PredicateValue) → List α → Colon →
      Except (AnyAllError ε) (Option Bool))
    (tupleImpl : (Bool → Option Bool) → (α → Except ε PredicateValue) → Bool → List α →
      Except (AnyAllError ε) (Option Bool))
    (done : Bool → Option Bool) (f : α → Except ε PredicateValue)
    (isNTuple : Bool) (itr : List α) : Except (AnyAllError ε) (Option Bool) :=
  if isNTuple || itr.length > 32 then
    anyImpl f itr .colon
  else
    tupleImpl done f false itr

/--
Julia source: base/anyall.jl:159-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _any_tuple(f, anymissing::Bool, x, rest...)
    v = f(x)
    if ismissing(v)
        anymissing = true
    elseif v
        return true
    end
    return _any_tuple(f, anymissing, rest...)
end
```
-/
def anyTupleStep {ε α : Type} (done : Bool → Option Bool)
    (f : α → Except ε PredicateValue) (anymissing : Bool) : List α →
    Except (AnyAllError ε) (Option Bool)
  | [] => .ok (done anymissing)
  | x :: rest =>
      match f x with
      | .error e => .error (.predicate e)
      | .ok .missing => anyTupleStep done f true rest
      | .ok (.bool true) => .ok (some true)
      | .ok (.bool false) => anyTupleStep done f anymissing rest
      | .ok .other => .error .typeError

/--
Julia source: base/anyall.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _any_tuple(_, anymissing::Bool) = anymissing ? missing : false
```
-/
def anyTupleDone (anymissing : Bool) : Option Bool :=
  if anymissing then none else some false

/--
Julia source: base/anyall.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
all(f, itr) = _all(f, itr, :)
```
-/
def allPredicate {ε I α : Type}
    (allImpl : (I → List α) → (α → Except ε PredicateValue) → I → Colon →
      Except (AnyAllError ε) (Option Bool))
    (items : I → List α) (f : α → Except ε PredicateValue) (itr : I) :
    Except (AnyAllError ε) (Option Bool) :=
  allImpl items f itr .colon

/--
Julia source: base/anyall.jl:207-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function _all(f, itr::$ItrT, ::Colon)
        $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
        anymissing = false
        for x in itr
            v = f(x)
            if ismissing(v)
                anymissing = true
            else
                v || return false
            end
        end
        return anymissing ? missing : true
    end
end
```
-/
def allTupleLoop {ε α : Type} (f : α → Except ε PredicateValue) (itr : List α)
    (_colon : Colon) : Except (AnyAllError ε) (Option Bool) :=
  let rec loop (anymissing : Bool) : List α → Except (AnyAllError ε) (Option Bool)
    | [] => .ok (if anymissing then none else some true)
    | x :: rest =>
        match f x with
        | .error e => .error (.predicate e)
        | .ok .missing => loop true rest
        | .ok (.bool false) => .ok (some false)
        | .ok (.bool true) => loop anymissing rest
        | .ok .other => .error .typeError
  loop false itr

/--
Julia source: base/anyall.jl:207-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function _all(f, itr::$ItrT, ::Colon)
        $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
        anymissing = false
        for x in itr
            v = f(x)
            if ismissing(v)
                anymissing = true
            else
                v || return false
            end
        end
        return anymissing ? missing : true
    end
end
```
-/
def allAny {ε I α : Type} (items : I → List α) (f : α → Except ε PredicateValue)
    (itr : I) (_colon : Colon) : Except (AnyAllError ε) (Option Bool) :=
  let rec loop (anymissing : Bool) : List α → Except (AnyAllError ε) (Option Bool)
    | [] => .ok (if anymissing then none else some true)
    | x :: rest =>
        match f x with
        | .error e => .error (.predicate e)
        | .ok .missing => loop true rest
        | .ok (.bool false) => .ok (some false)
        | .ok (.bool true) => loop anymissing rest
        | .ok .other => .error .typeError
  loop false (items itr)

/--
Julia source: base/anyall.jl:224-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _all(::typeof(identity), itr::Tuple{Vararg{Bool}}, ::Colon)
    @_terminates_locally_meta
    r = true
    for i in eachindex(itr)
        # Avoid bounds checking to help vectorization. Use `getfield` directly,
        # instead of `@inbounds itr[i]`, for better effects.
        v = getfield(itr, i, false)
        r &= v
    end
    r
end
```
-/
def allBoolTuple (itr : List Bool) (_colon : Colon) : Bool :=
  itr.foldl (fun r value => r && value) true

/--
Julia source: base/anyall.jl:238-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function all(f, itr::Tuple)
    if itr isa NTuple || length(itr) > 32
        return _all(f, itr, :)
    end
    _all_tuple(f, false, itr...)
end
```
-/
def allTupleMethod {ε α : Type}
    (allImpl : (α → Except ε PredicateValue) → List α → Colon →
      Except (AnyAllError ε) (Option Bool))
    (tupleImpl : (Bool → Option Bool) → (α → Except ε PredicateValue) → Bool → List α →
      Except (AnyAllError ε) (Option Bool))
    (done : Bool → Option Bool) (f : α → Except ε PredicateValue)
    (isNTuple : Bool) (itr : List α) : Except (AnyAllError ε) (Option Bool) :=
  if isNTuple || itr.length > 32 then
    allImpl f itr .colon
  else
    tupleImpl done f false itr

/--
Julia source: base/anyall.jl:245-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _all_tuple(f, anymissing::Bool, x, rest...)
    v = f(x)
    if ismissing(v)
        anymissing = true
    # this syntax allows throwing a TypeError for non-Bool, for consistency with any
    elseif v
        nothing
    else
        return false
    end
    return _all_tuple(f, anymissing, rest...)
end
```
-/
def allTupleStep {ε α : Type} (done : Bool → Option Bool)
    (f : α → Except ε PredicateValue) (anymissing : Bool) : List α →
    Except (AnyAllError ε) (Option Bool)
  | [] => .ok (done anymissing)
  | x :: rest =>
      match f x with
      | .error e => .error (.predicate e)
      | .ok .missing => allTupleStep done f true rest
      | .ok (.bool true) => allTupleStep done f anymissing rest
      | .ok (.bool false) => .ok (some false)
      | .ok .other => .error .typeError

/--
Julia source: base/anyall.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
```
-/
def allTupleDone (anymissing : Bool) : Option Bool :=
  if anymissing then none else some true

/-- Dispatch adapters for source calls through Julia's overloaded `any` and `all`. -/
def anyValueCall {ε I : Type} (items : I → List PredicateValue)
    (f : PredicateValue → Except ε PredicateValue) (itr : I) :
    Except (AnyAllError ε) (Option Bool) :=
  anyPredicate anyAny items f itr

def allValueCall {ε I : Type} (items : I → List PredicateValue)
    (f : PredicateValue → Except ε PredicateValue) (itr : I) :
    Except (AnyAllError ε) (Option Bool) :=
  allPredicate allAny items f itr

def anyBoolTupleCall {ε : Type} (_f : Bool → Except ε PredicateValue)
    (itr : List Bool) (c : Colon) : Except (AnyAllError ε) (Option Bool) :=
  .ok (some (anyBoolTuple itr c))

def allBoolTupleCall {ε : Type} (_f : Bool → Except ε PredicateValue)
    (itr : List Bool) (c : Colon) : Except (AnyAllError ε) (Option Bool) :=
  .ok (some (allBoolTuple itr c))

end JuliaLean.base.anyall

namespace JuliaLean.IteratorsCov

inductive Truth where
  | false_ | true_ | missing | other
  deriving Repr, DecidableEq

abbrev TruthResult := R (Option Bool)

/-- The generated `_any(f, itr, :)` loop at `base/anyall.jl:120-132`. -/
def anyLoop : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some false)
  | _, .true_ :: _ => .ok (some true)
  | anymissing, .false_ :: rest => anyLoop anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => anyLoop true rest

/-- The recursive `_any_tuple` methods at `base/anyall.jl:159-168`. -/
def anyTuple : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some false)
  | _, .true_ :: _ => .ok (some true)
  | anymissing, .false_ :: rest => anyTuple anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => anyTuple true rest

/-- The side-effect-free Bool tuple specialization at `base/anyall.jl:137-147`. -/
def anyBoolTuple : List Bool → Bool
  | [] => false
  | x :: xs => x || anyBoolTuple xs

/-- `any(itr) = any(identity, itr)` (41) and `any(f, itr) = _any(f, itr, :)`
(115), after applying the predicate. -/
def anyIdentity (xs : List Truth) : TruthResult := anyLoop false xs
def anyPred (f : α → Truth) (xs : List α) : TruthResult := anyLoop false (xs.map f)

/-- The generated `_all(f, itr, :)` loop at `base/anyall.jl:207-219`. -/
def allLoop : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some true)
  | _, .false_ :: _ => .ok (some false)
  | anymissing, .true_ :: rest => allLoop anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => allLoop true rest

/-- The recursive `_all_tuple` methods at `base/anyall.jl:245-257`. -/
def allTuple : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some true)
  | _, .false_ :: _ => .ok (some false)
  | anymissing, .true_ :: rest => allTuple anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => allTuple true rest

/-- The side-effect-free Bool tuple specialization at `base/anyall.jl:224-234`. -/
def allBoolTuple : List Bool → Bool
  | [] => true
  | x :: xs => x && allBoolTuple xs

/-- `all(itr) = all(identity, itr)` (80) and `all(f, itr) = _all(f, itr, :)`
(202), after applying the predicate. -/
def allIdentity (xs : List Truth) : TruthResult := allLoop false xs
def allPred (f : α → Truth) (xs : List α) : TruthResult := allLoop false (xs.map f)

end JuliaLean.IteratorsCov

namespace JuliaLean.Reduce.Vec

/-- `any(f, itr)`, `base/anyall.jl:115-130`: short-circuits on the first `true`; a
non-`Bool`, non-`missing` value of `f` throws `TypeError` in `v && return true`. -/
def any (f : Val → Val) : List Val → R Val
  | [] => .ok (.bool false)
  | x :: rest =>
    match f x with
    | .missing => (any f rest).map fun r => if r = .bool false then .missing else r
    | .bool true => .ok (.bool true)
    | .bool false => any f rest
    | _ => .error .typeError

/-- `all(f, itr)`, `base/anyall.jl:202-217`. -/
def all (f : Val → Val) : List Val → R Val
  | [] => .ok (.bool true)
  | x :: rest =>
    match f x with
    | .missing => (all f rest).map fun r => if r = .bool true then .missing else r
    | .bool false => .ok (.bool false)
    | .bool true => all f rest
    | _ => .error .typeError

end JuliaLean.Reduce.Vec
