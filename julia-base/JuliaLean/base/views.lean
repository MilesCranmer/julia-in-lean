import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.subarray

/-!
# Source-mirrored model of `base/views.jl`

Julia AST values are represented by `ViewSyntax`. External macro expansion and
expression construction stay explicit hooks. `mapany` uses list mapping.
-/

namespace JuliaLean.base.views

inductive ViewSyntax where
  | symbol (name : String)
  | generated (tag : String) (serial : Nat)
  | expr (head : String) (args : List ViewSyntax)
  | integer (value : Nat)
  | global (name : String)
  | opaque (name : String)
  deriving Repr, BEq, Inhabited

inductive ViewError where
  | errorException (message : String)
  | argumentError (message : String)
  | assertionError (message : String)
  | boundsError
  deriving Repr, BEq

/-- `none` denotes divergence; terminating outcomes preserve Julia's value or exception.
The state is the next unused serial in Julia's fresh-symbol supply. -/
abbrev ViewResult (α : Type) := StateT Nat (ExceptT ViewError Option) α

def isExpr (value : ViewSyntax) (head : String) : Bool :=
  match value with
  | .expr actual _ => actual == head
  | _ => false

def syntaxArgs (value : ViewSyntax) : List ViewSyntax :=
  match value with
  | .expr _ args => args
  | _ => []

def syntaxArg (args : List ViewSyntax) (index : Nat) : ViewResult ViewSyntax :=
  match args[index]? with
  | some value => pure value
  | none => throw .boundsError

def syntaxCall (fn : ViewSyntax) (args : List ViewSyntax) : ViewSyntax :=
  .expr "call" (fn :: args)

def setListAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: rest, 0, value => value :: rest
  | item :: rest, index + 1, value => item :: setListAt rest index value

def updateAtPath (root : ViewSyntax) (path : List Nat) (replacement : ViewSyntax) : ViewSyntax :=
  match path with
  | [] => replacement
  | index :: rest =>
      match root with
      | .expr head args =>
          let child := args.getD index (.opaque "missing-expression")
          .expr head (setListAt args index (updateAtPath child rest replacement))
      | _ => root

def indexList {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | index, value :: rest => (index, value) :: indexList (index + 1) rest

def prepareOpIndices (indices : List ViewSyntax) : ViewResult (List (ViewSyntax × ViewSyntax)) :=
  (indexList 1 indices).mapM
    (fun (position, index) => do
      let indexVariable := ViewSyntax.symbol ("i" ++ toString position)
      if isExpr index "..." then
        let value ← syntaxArg (syntaxArgs index) 0
        pure (.expr "..." [indexVariable], value)
      else pure (indexVariable, index))

def endsInEquals (value : String) : Bool := value.toList.getLast? == some '='

def startsInDot (value : String) : Bool := value.toList.head? == some '.'

def dropLastChar (value : String) : String :=
  String.ofList (value.toList.take (value.length - 1))

def escapeSyntax (value : ViewSyntax) : ViewSyntax := .expr "escape" [value]

/--
Julia source: base/views.jl:22-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function escapes(@nospecialize(ex), escs::Int)
        for _ = 1:escs
            ex = esc(ex)
        end
        return ex
    end
```
-/
def escapes (value : ViewSyntax) (depth : Int) : ViewSyntax :=
  (List.range depth.toNat).foldl (fun result _ => escapeSyntax result) value

def firstIndexExpr (array : ViewSyntax) (index : Option ViewSyntax := none) : ViewSyntax :=
  syntaxCall (.global "Base.firstindex") (array :: index.toList)

def lastIndexExpr (array : ViewSyntax) (index : Option ViewSyntax := none) : ViewSyntax :=
  syntaxCall (.global "Base.lastindex") (array :: index.toList)

structure ReplaceHooks (Module : Type) where
  /-- `macroexpand(module, ex)` expands a macro call in that module and propagates its Julia error. -/
  macroexpand : Module → ViewSyntax → ViewResult ViewSyntax
  /-- `isa_ast_node(ex)` reports whether Julia treats the value as an AST node. -/
  isAstNode : ViewSyntax → Bool

def freshSyntax {Module : Type} (_hooks : ReplaceHooks Module) (tag : String) : ViewResult ViewSyntax := do
  let serial ← get
  set (serial + 1)
  pure (.generated tag serial)

/-- The Julia parameter tuple `(__module__, withex, in_quote_context, escs)` that boundary
replacement threads through every recursive call. -/
structure ReplaceCtx (Module : Type) where
  owner : Module
  withex : Option (ViewSyntax × ViewSyntax)
  inQuoteContext : Bool
  escapeDepth : Int

/--
Julia source: base/views.jl:112-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    if isa(ex,Symbol)
        if !in_quote_context
            if ex === :begin
                withex === nothing && error("Invalid use of begin outside []")
                return escapes((withex::NTuple{2,Expr})[1], escs), true
            elseif ex === :end
                withex === nothing && error("Invalid use of end outside []")
                return escapes((withex::NTuple{2,Expr})[2], escs), true
            end
        end
```
-/
@[irreducible]
def boundaryOutcome (inQuoteContext : Bool) (withex : Option (ViewSyntax × ViewSyntax))
    (escapeDepth : Int) (name : String) (unchanged : ViewSyntax)
    (beginError endError : ViewError) : ViewResult (ViewSyntax × Bool) :=
  if (name == "begin" || name == "end") && inQuoteContext then pure (unchanged, false)
  else if name == "begin" then
    match withex with
    | some (first, _) => pure (escapes first escapeDepth, true)
    | none => throw beginError
  else if name == "end" then
    match withex with
    | some (_, last) => pure (escapes last escapeDepth, true)
    | none => throw endError
  else pure (unchanged, false)

def isZeroDimension : ViewSyntax → Bool
  | .integer value => value == 0
  | _ => false

structure RefScan where
  args : List ViewSyntax
  position : Nat
  nextIndex : Nat
  expandedIndexCount : ViewSyntax
  usedBoundary : Bool
  needTemps : Bool
  temporaries : List (Nat × ViewSyntax)



mutual
  /--
Julia source: base/views.jl:19-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace_ref_begin_end_!(__module__::Module, ex, withex, in_quote_context::Bool, escs::Int)
    @nospecialize
    used_withex = false
    function escapes(@nospecialize(ex), escs::Int)
        for _ = 1:escs
            ex = esc(ex)
        end
        return ex
    end
    function handle_refexpr!(__module__::Module, ref_ex::Expr, main_ex::Expr, withex, in_quote_context, escs::Int)
        @assert !in_quote_context "handle_refexpr! should not be called in quote context"
        local used_withex
        ref_ex.args[1], used_withex = replace_ref_begin_end_!(__module__, ref_ex.args[1], withex, in_quote_context, escs)
        S = gensym(:S) # temp var to cache ex.args[1] if needed. if S is a global or expression, then it has side effects to use
        assignments = []
        used_S = false # whether we actually need S
        # new :ref, so redefine withex
        nargs = length(ref_ex.args) - 1
        if nargs == 0
            return main_ex, used_withex
        elseif nargs == 1
            # replace with lastindex(S)
            ref_ex.args[2], used_S = replace_ref_begin_end_!(__module__, ref_ex.args[2], (:($firstindex($S)),:($lastindex($S))), in_quote_context, escs)
        else
            ni = 1
            nx = 0
            J = nargs + 1
            need_temps = false # whether any arg needs temporaries

            # First pass: determine if any argument will needs temporaries
            for j = 2:J
                exj = ref_ex.args[j]
                if isexpr(exj, :...)
                    need_temps = true
                    break
                end
            end

            # Second pass: if any need temps, create temps for all args
            temp_vars = Tuple{Int,Symbol}[]
            for j = 2:J
                n = nx === 0 ? ni : :($nx + $ni)
                exj, used_arg = replace_ref_begin_end_!(__module__, ref_ex.args[j], (:($firstindex($S,$n)),:($lastindex($S,$n))), in_quote_context, escs)
                used_S |= used_arg
                ref_ex.args[j] = exj
                ni += 1
                if need_temps
                    isva = isexpr(exj, :...) # implied need_temps
                    if isva
                        exj = exj.args[1]
                    end
                    if isa_ast_node(exj) # create temp to preserve evaluation order and count in case `used` gets set later
                        exj = gensym(:arg)
                        push!(temp_vars, (j, exj))
                    end
                    if isva
                        ni -= 1
                        nx = nx === 0 ? :(length($exj)) : :($nx + length($exj))
                    end
                end
            end

            # Third pass: if `used`, need to actually make those temp assignments now
            if used_S
                for (j, temp_var) in temp_vars
                    exj = ref_ex.args[j]
                    isva = isexpr(exj, :...) # implied need_temps
                    if isva
                        exj = exj.args[1]
                    end
                    push!(assignments, :(local $temp_var = $exj))
                    ref_ex.args[j] = isva ? Expr(:..., temp_var) : temp_var
                end
            end
        end

        if used_S
            S0 = ref_ex.args[1]
            S = escapes(S, escs)
            ref_ex.args[1] = S
            main_ex = :(local $S = $S0; $(assignments...); $main_ex)
        end
        return main_ex, used_withex
    end
    if ex isa Expr && ex.head === :macrocall
        # Blithely modifying the arguments to another macro is unwise, so call
        # macroexpand first on it.
        # Unfortunately, macroexpand itself corrupts the scope of variables in
        # the result by calling macroexpand.scm before returning which cannot be
        # avoided since `jl_expand_macros` is private and somewhat difficult to
        # reimplement correctly.
        ex = macroexpand(__module__, ex)
    end
    if isa(ex,Symbol)
        if !in_quote_context
            if ex === :begin
                withex === nothing && error("Invalid use of begin outside []")
                return escapes((withex::NTuple{2,Expr})[1], escs), true
            elseif ex === :end
                withex === nothing && error("Invalid use of end outside []")
                return escapes((withex::NTuple{2,Expr})[2], escs), true
            end
        end
    elseif isa(ex,Expr)
        if !in_quote_context && ex.head === :ref # n.b. macroexpand.scm design is incapable of tracking :begin and :end scope, so emulate that here too and ignore escs
            return handle_refexpr!(__module__, ex, ex, withex, in_quote_context, escs)
        elseif ex.head === :$
            # no longer an executable expression (handle all equivalent forms of :inert, :quote, and QuoteNode the same way)
            in_quote_context = false
        elseif ex.head === :quote
            # executable again
            in_quote_context = true
        elseif ex.head === :var"hygienic-scope"
            # no longer our expression
            escs += 1
        elseif ex.head === :escape
            # our expression again once zero
            escs == 0 && return ex, used_withex
            escs -= 1
        elseif ex.head === :meta || ex.head === :inert
            return ex, used_withex
        elseif !in_quote_context && last(string(ex.head)) == '=' && Meta.isexpr(ex.args[1], :ref)
            for i = eachindex(ex.args)
                if i == 1
                    # we'll deal with the ref expression later
                    continue
                end
                ex.args[i], used = replace_ref_begin_end_!(__module__, ex.args[i], withex, in_quote_context, escs)
                used_withex |= used
            end
            ex, used = handle_refexpr!(__module__, ex.args[1]::Expr, ex, withex, in_quote_context, escs)
            used_withex |= used
            return ex, used_withex
        end
        # recursive search
        for i = eachindex(ex.args)
            ex.args[i], used = replace_ref_begin_end_!(__module__, ex.args[i], withex, in_quote_context, escs)
            used_withex |= used
        end
    end
    return ex, used_withex
end
```
  -/
  def replace_ref_begin_end_! {Module : Type} (hooks : ReplaceHooks Module)
      (ctx : ReplaceCtx Module) (expression : ViewSyntax) : ViewResult (ViewSyntax × Bool) := do
    if isExpr expression "macrocall" then do
      let expanded ← hooks.macroexpand ctx.owner expression
      dispatchExpanded hooks ctx expanded
    else
      dispatchExpanded hooks ctx expression
  partial_fixpoint

  /-- The dispatch body of `replace_ref_begin_end_!` after the macrocall expansion step. -/
  def dispatchExpanded {Module : Type} (hooks : ReplaceHooks Module)
      (ctx : ReplaceCtx Module) (expanded : ViewSyntax) : ViewResult (ViewSyntax × Bool) := do
    match expanded with
    | .symbol name => do
        let outcome ← boundaryOutcome ctx.inQuoteContext ctx.withex ctx.escapeDepth name expanded
          (.errorException "Invalid use of begin outside []")
          (.errorException "Invalid use of end outside []")
        pure outcome
    | .generated _ _ => pure (expanded, false)
    | .integer _ => pure (expanded, false)
    | .global _ => pure (expanded, false)
    | .opaque _ => pure (expanded, false)
    | .expr head args =>
        if !ctx.inQuoteContext && head == "ref" then
          handle_refexpr! hooks ctx expanded expanded []
        else if head == "meta" || head == "inert" then
          pure (expanded, false)
        else if head == "escape" && ctx.escapeDepth == 0 then
          pure (expanded, false)
        else if !ctx.inQuoteContext && head == "" then
          throw .boundsError
        else if !ctx.inQuoteContext && endsInEquals head && args.isEmpty then
          throw .boundsError
        else if !ctx.inQuoteContext && endsInEquals head &&
            args.head?.any (fun first => isExpr first "ref") then
          match args with
          | first :: rest =>
              let otherResults ← replaceArgs hooks ctx rest
              let rewrittenArgs := [first] ++ otherResults.map Prod.fst
              let rewrittenMain := .expr head rewrittenArgs
              let (result, usedRef) ←
                handle_refexpr! hooks ctx first rewrittenMain [0]
              pure (result, usedRef || otherResults.any Prod.snd)
          | [] => throw .boundsError
        else
          let childCtx : ReplaceCtx Module :=
            { owner := ctx.owner, withex := ctx.withex,
              inQuoteContext :=
                if head == "$" then false else if head == "quote" then true else ctx.inQuoteContext,
              escapeDepth :=
                if head == "hygienic-scope" then ctx.escapeDepth + 1
                else if head == "escape" then ctx.escapeDepth - 1
                else ctx.escapeDepth }
          let children ← replaceArgs hooks childCtx args
          pure (.expr head (children.map Prod.fst), children.any Prod.snd)
  partial_fixpoint

  /--
Julia source: base/views.jl:28-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function handle_refexpr!(__module__::Module, ref_ex::Expr, main_ex::Expr, withex, in_quote_context, escs::Int)
        @assert !in_quote_context "handle_refexpr! should not be called in quote context"
        local used_withex
        ref_ex.args[1], used_withex = replace_ref_begin_end_!(__module__, ref_ex.args[1], withex, in_quote_context, escs)
        S = gensym(:S) # temp var to cache ex.args[1] if needed. if S is a global or expression, then it has side effects to use
        assignments = []
        used_S = false # whether we actually need S
        # new :ref, so redefine withex
        nargs = length(ref_ex.args) - 1
        if nargs == 0
            return main_ex, used_withex
        elseif nargs == 1
            # replace with lastindex(S)
            ref_ex.args[2], used_S = replace_ref_begin_end_!(__module__, ref_ex.args[2], (:($firstindex($S)),:($lastindex($S))), in_quote_context, escs)
        else
            ni = 1
            nx = 0
            J = nargs + 1
            need_temps = false # whether any arg needs temporaries

            # First pass: determine if any argument will needs temporaries
            for j = 2:J
                exj = ref_ex.args[j]
                if isexpr(exj, :...)
                    need_temps = true
                    break
                end
            end

            # Second pass: if any need temps, create temps for all args
            temp_vars = Tuple{Int,Symbol}[]
            for j = 2:J
                n = nx === 0 ? ni : :($nx + $ni)
                exj, used_arg = replace_ref_begin_end_!(__module__, ref_ex.args[j], (:($firstindex($S,$n)),:($lastindex($S,$n))), in_quote_context, escs)
                used_S |= used_arg
                ref_ex.args[j] = exj
                ni += 1
                if need_temps
                    isva = isexpr(exj, :...) # implied need_temps
                    if isva
                        exj = exj.args[1]
                    end
                    if isa_ast_node(exj) # create temp to preserve evaluation order and count in case `used` gets set later
                        exj = gensym(:arg)
                        push!(temp_vars, (j, exj))
                    end
                    if isva
                        ni -= 1
                        nx = nx === 0 ? :(length($exj)) : :($nx + length($exj))
                    end
                end
            end

            # Third pass: if `used`, need to actually make those temp assignments now
            if used_S
                for (j, temp_var) in temp_vars
                    exj = ref_ex.args[j]
                    isva = isexpr(exj, :...) # implied need_temps
                    if isva
                        exj = exj.args[1]
                    end
                    push!(assignments, :(local $temp_var = $exj))
                    ref_ex.args[j] = isva ? Expr(:..., temp_var) : temp_var
                end
            end
        end

        if used_S
            S0 = ref_ex.args[1]
            S = escapes(S, escs)
            ref_ex.args[1] = S
            main_ex = :(local $S = $S0; $(assignments...); $main_ex)
        end
        return main_ex, used_withex
    end
```
  -/
  def handle_refexpr! {Module : Type} (hooks : ReplaceHooks Module)
      (ctx : ReplaceCtx Module) (refExpression mainExpression : ViewSyntax)
      (mainPath : List Nat) : ViewResult (ViewSyntax × Bool) := do
    if ctx.inQuoteContext then throw (.assertionError "handle_refexpr! should not be called in quote context")
    match refExpression with
    | .expr _ [] => throw .boundsError
    | .expr _ (originalArray :: indexArgs) =>
        let (array, usedArray) ←
          replace_ref_begin_end_! hooks ctx originalArray
        let generatedS ← freshSyntax hooks "S"
        let refArgs := array :: indexArgs
        match indexArgs with
        | [] =>
            pure (updateAtPath mainExpression mainPath (.expr "ref" refArgs), usedArray)
        | [index] =>
            let first := firstIndexExpr generatedS
            let last := lastIndexExpr generatedS
            let (rewrittenIndex, usedIndex) ←
              replace_ref_begin_end_! hooks { ctx with withex := some (first, last) } index
            let rewrittenArgs := setListAt refArgs 1 rewrittenIndex
            if usedIndex then
              let escapedS := escapes generatedS ctx.escapeDepth
              let cachedArgs := setListAt rewrittenArgs 0 escapedS
              let main := updateAtPath mainExpression mainPath (.expr "ref" cachedArgs)
              let binding := .expr "local" [.expr "=" [escapedS, array]]
              pure (.expr "block" [binding, main], usedArray)
            else
              pure (updateAtPath mainExpression mainPath (.expr "ref" rewrittenArgs), usedArray)
        | _ :: _ =>
            let initial : RefScan :=
              { args := refArgs, position := 0, nextIndex := 1, expandedIndexCount := .integer 0,
                usedBoundary := false,
                needTemps := indexArgs.any (fun index => isExpr index "..."),
                temporaries := [] }
            let scan ← scanStep hooks ctx generatedS indexArgs initial
            let (rewrittenArgs, assignments) ←
              if scan.usedBoundary then
                scan.temporaries.foldlM
                  (fun (args, assignments) (indexPosition, temp) => do
                    let value ← syntaxArg args indexPosition
                    let isSplat := isExpr value "..."
                    let assignedValue ←
                      if isSplat then syntaxArg (syntaxArgs value) 0 else pure value
                    let replacement := if isSplat then .expr "..." [temp] else temp
                    pure (setListAt args indexPosition replacement,
                      assignments ++ [.expr "local" [.expr "=" [temp, assignedValue]]]))
                  (scan.args, [])
              else pure (scan.args, [])
            if scan.usedBoundary then
              let sourceArray ← syntaxArg rewrittenArgs 0
              let escapedS := escapes generatedS ctx.escapeDepth
              let cachedArgs := setListAt rewrittenArgs 0 escapedS
              let main := updateAtPath mainExpression mainPath (.expr "ref" cachedArgs)
              let binding := .expr "local" [.expr "=" [escapedS, sourceArray]]
              pure (.expr "block" ([binding] ++ assignments ++ [main]), usedArray)
            else
              let main := updateAtPath mainExpression mainPath (.expr "ref" rewrittenArgs)
              pure (main, usedArray)
    | _ => throw .boundsError
  partial_fixpoint

  /--
Julia source: base/views.jl:59-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            for j = 2:J
                n = nx === 0 ? ni : :($nx + $ni)
                exj, used_arg = replace_ref_begin_end_!(__module__, ref_ex.args[j], (:($firstindex($S,$n)),:($lastindex($S,$n))), in_quote_context, escs)
                used_S |= used_arg
                ref_ex.args[j] = exj
                ni += 1
                if need_temps
                    isva = isexpr(exj, :...) # implied need_temps
                    if isva
                        exj = exj.args[1]
                    end
                    if isa_ast_node(exj) # create temp to preserve evaluation order and count in case `used` gets set later
                        exj = gensym(:arg)
                        push!(temp_vars, (j, exj))
                    end
                    if isva
                        ni -= 1
                        nx = nx === 0 ? :(length($exj)) : :($nx + length($exj))
                    end
                end
            end
```
  -/
  def scanStep {Module : Type} (hooks : ReplaceHooks Module)
      (ctx : ReplaceCtx Module) (generatedS : ViewSyntax)
      : List ViewSyntax → RefScan → ViewResult RefScan
    | [], scan => pure scan
    | indexExpression :: rest, scan => do
        let dimension :=
          if isZeroDimension scan.expandedIndexCount then .integer scan.nextIndex
          else syntaxCall (.global "Base.+") [scan.expandedIndexCount, .integer scan.nextIndex]
        let boundaries := (firstIndexExpr generatedS (some dimension), lastIndexExpr generatedS (some dimension))
        let (rewrittenIndex, usedIndex) ←
          replace_ref_begin_end_! hooks { ctx with withex := some boundaries } indexExpression
        let storedArgs := setListAt scan.args (scan.position + 1) rewrittenIndex
        let isSplat := isExpr rewrittenIndex "..."
        let mut valueForLength := rewrittenIndex
        let mut nextIndex := scan.nextIndex + 1
        let mut expandedIndexCount := scan.expandedIndexCount
        let mut temporaries := scan.temporaries
        if scan.needTemps then
          if isSplat then valueForLength ← syntaxArg (syntaxArgs rewrittenIndex) 0
          if hooks.isAstNode valueForLength then
            let temp ← freshSyntax hooks "arg"
            temporaries := temporaries ++ [(scan.position + 1, temp)]
            valueForLength := temp
          if isSplat then
            nextIndex := nextIndex - 1
            let size := syntaxCall (.global "Base.length") [valueForLength]
            expandedIndexCount :=
              if isZeroDimension scan.expandedIndexCount then size
              else syntaxCall (.global "Base.+") [scan.expandedIndexCount, size]
        scanStep hooks ctx generatedS rest
          { args := storedArgs, position := scan.position + 1, nextIndex := nextIndex,
            expandedIndexCount := expandedIndexCount,
            usedBoundary := scan.usedBoundary || usedIndex, needTemps := scan.needTemps,
            temporaries := temporaries }
  partial_fixpoint

  /--
Julia source: base/views.jl:153-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        # recursive search
        for i = eachindex(ex.args)
            ex.args[i], used = replace_ref_begin_end_!(__module__, ex.args[i], withex, in_quote_context, escs)
            used_withex |= used
        end
```
  -/
  def replaceArgs {Module : Type} (hooks : ReplaceHooks Module)
      (ctx : ReplaceCtx Module) : List ViewSyntax → ViewResult (List (ViewSyntax × Bool))
    | [] => pure []
    | child :: rest => do
        let head ← replace_ref_begin_end_! hooks ctx child
        let tail ← replaceArgs hooks ctx rest
        pure (head :: tail)
  partial_fixpoint
end

/--
Julia source: base/views.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace_ref_begin_end!(__module__::Module, @nospecialize ex) = replace_ref_begin_end_!(__module__, ex, nothing, false, 0)[1]
```
-/
def replace_ref_begin_end! {Module : Type} (hooks : ReplaceHooks Module)
    (moduleValue : Module) (expression : ViewSyntax) : ViewResult ViewSyntax := do
  let (result, _) ← replace_ref_begin_end_! hooks
    { owner := moduleValue, withex := none, inQuoteContext := false, escapeDepth := 0 } expression
  pure result
/--
Julia source: base/views.jl:210-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro view(ex)
    Meta.isexpr(ex, :ref) || throw(ArgumentError(
        "Invalid use of @view macro: argument must be a reference expression A[...]."))
    ex = replace_ref_begin_end!(__module__, ex)
    # NOTE We embed `view` as a function object itself directly into the AST.
    #      By doing this, we prevent the creation of function definitions like
    #      `view(A, idx) = xxx` in cases such as `@view(A[idx]) = xxx.`
    if Meta.isexpr(ex, :ref)
        ex = Expr(:call, view, ex.args...)
    elseif Meta.isexpr(ex, :block)
        arg2 = ex.args[end]
        Meta.isexpr(arg2, :ref) || error("unsupported replace_ref_begin_end result")
        # ex replaced by let ...; foo[...]; end
        ex.args[end] = Expr(:call, view, arg2.args...)
    else
        error("unsupported replace_ref_begin_end result")
    end
    return esc(ex)
end
```
-/
def viewMacro {Module : Type} (hooks : ReplaceHooks Module)
    (moduleValue : Module) (expression : ViewSyntax) : ViewResult ViewSyntax := do
  if !isExpr expression "ref" then
    throw (.argumentError "Invalid use of @view macro: argument must be a reference expression A[...].")
  let expression ← replace_ref_begin_end! hooks moduleValue expression
  match expression with
  | .expr "ref" args => pure (escapeSyntax (syntaxCall (.global "Base.view") args))
  | .expr "block" args =>
      match args.getLast? with
      | none => throw .boundsError
      | some (.expr "ref" refArgs) =>
          let rewritten := setListAt args (args.length - 1) (syntaxCall (.global "Base.view") refArgs)
          pure (escapeSyntax (.expr "block" rewritten))
      | some _ => throw (.errorException "unsupported replace_ref_begin_end result")
  | _ => throw (.errorException "unsupported replace_ref_begin_end result")

class AbstractArrayType (A : Type) where
  dimensions : A → List Nat

class NumberType (N : Type) where
  toInteger : N → Except ViewError Int

class AbstractCartesianIndexType (C : Type) where
  coordinates : C → List Int

inductive ScalarViewIndex (N C : Type) where
  | number (value : N)
  | cartesian (value : C)

instance : NumberType Int where
  toInteger := Except.ok

instance : AbstractCartesianIndexType (List Int) where
  coordinates := id

instance {Tag : Type} : AbstractArrayType (JuliaLean.base.array.HeapArray Tag) where
  dimensions := JuliaLean.base.array.HeapArray.dimensions

/--
Julia source: base/views.jl:235-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds maybeview(A, args...) = getindex(A, args...)
```
-/
def maybeviewGeneric {A Args R E : Type} (getindex : A → Args → Except E R)
    (array : A) (args : Args) : Except E R := getindex array args

/--
Julia source: base/views.jl:236-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds maybeview(A::AbstractArray, args...) = view(A, args...)
```
-/
def maybeviewArray {A Args R E : Type} [AbstractArrayType A] (view : A → Args → Except E R)
    (array : A) (args : Args) : Except E R := view array args

/--
Julia source: base/views.jl:237-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds maybeview(A::AbstractArray, args::Union{Number,AbstractCartesianIndex}...) = getindex(A, args...)
```
-/
def maybeviewArrayScalarIndices {A N C R E : Type}
    [AbstractArrayType A] [NumberType N] [AbstractCartesianIndexType C]
    (getindex : A → List (ScalarViewIndex N C) → Except E R)
    (array : A) (args : List (ScalarViewIndex N C)) : Except E R := getindex array args

/--
Julia source: base/views.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds maybeview(A) = getindex(A)
```
-/
def maybeviewGenericZero {A R E : Type} (getindex : A → Except E R)
    (array : A) : Except E R := getindex array

/--
Julia source: base/views.jl:239-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds maybeview(A::AbstractArray) = getindex(A)
```
-/
def maybeviewArrayZero {A R E : Type} [AbstractArrayType A] (getindex : A → Except E R)
    (array : A) : Except E R := getindex array

structure HeapViewOps (Tag : Type) where
  unalias : JuliaLean.base.array.HeapArray Tag → JuliaLean.base.subarray.Index →
    JuliaLean.base.subarray.Index
  normalize : JuliaLean.base.array.HeapArray Tag → List JuliaLean.base.subarray.Index →
    List JuliaLean.base.subarray.Index
  checkBounds : JuliaLean.base.array.HeapArray Tag → List JuliaLean.base.subarray.Index →
    JuliaLean.Jl Unit
  removeSingletons : List Bool → List JuliaLean.base.subarray.Index →
    List JuliaLean.base.subarray.Index
  indexNdims : List JuliaLean.base.subarray.Index → List Bool

def heapView {Tag T : Type} (ops : HeapViewOps Tag)
    (array : JuliaLean.base.array.HeapArray Tag) (indices : List JuliaLean.base.subarray.Index) :
    JuliaLean.Jl (JuliaLean.base.subarray.SubArray (JuliaLean.base.array.HeapArray Tag) T) :=
  JuliaLean.base.subarray.viewArray array indices ops.unalias ops.normalize ops.checkBounds
    (fun parent => parent.dimensions.length) ops.removeSingletons
    JuliaLean.base.subarray.maybeReshapeParentSameRank ops.indexNdims
    (fun parent normalized =>
      JuliaLean.base.subarray.unsafeViewArray parent normalized
        (fun parent normalized =>
          JuliaLean.base.subarray.subarrayCartesian parent normalized (ops.indexNdims normalized)
            (fun parent normalized =>
              JuliaLean.base.subarray.checkParentIndexMatchArray parent (ops.indexNdims normalized))))

/--
Julia source: base/views.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_views(x) = x
```
-/
def viewsIdentity {α : Type} (expression : α) : α := expression

structure ViewsHooks where
  /-- `exprarray(head, args)` constructs an Expr with the supplied head and arguments. -/
  exprarray : String → List ViewSyntax → ViewSyntax

mutual
  def viewsAny (hooks : ViewsHooks) : ViewSyntax → ViewResult ViewSyntax
    | .expr head args => viewsExpr hooks head args
    | other => pure (viewsIdentity other)
  partial_fixpoint

  /--
Julia source: base/views.jl:248-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _views(ex::Expr)
    if ex.head in (:(=), :(.=))
        # don't use view for ref on the lhs of an assignment,
        # but still use views for the args of the ref:
        arg1 = ex.args[1]
        Expr(ex.head, Meta.isexpr(arg1, :ref) ?
                        Expr(:ref, mapany(_views, (arg1::Expr).args)...) : _views(arg1),
                _views(ex.args[2]))
    elseif ex.head === :ref
        Expr(:call, maybeview, mapany(_views, ex.args)...)::Expr
    else
        h = string(ex.head)
        # don't use view on the lhs of an op-assignment a[i...] += ...
        if last(h) == '=' && Meta.isexpr(ex.args[1], :ref)
            lhs = ex.args[1]::Expr

            # temp vars to avoid recomputing a and i,
            # which will be assigned in a let block:
            i = Symbol[Symbol(:i, k) for k = 1:length(lhs.args)-1]

            # for splatted indices like a[i, j...], we need to
            # splat the corresponding temp var.
            I = similar(i, Any)
            for k = 1:length(i)
                argk1 = lhs.args[k+1]
                if Meta.isexpr(argk1, :...)
                    I[k] = Expr(:..., i[k])
                    lhs.args[k+1] = (argk1::Expr).args[1] # unsplat
                else
                    I[k] = i[k]
                end
            end

            Expr(:var"hygienic-scope", # assign a and i to the macro's scope
                 Expr(:let,
                      Expr(:block,
                           :(a = $(esc(_views(lhs.args[1])))),
                           Any[:($(i[k]) = $(esc(_views(lhs.args[k+1])))) for k=1:length(i)]...),
                      Expr(first(h) == '.' ? :(.=) : :(=), :(a[$(I...)]),
                           Expr(:call, esc(Symbol(h[1:end-1])),
                                :($maybeview(a, $(I...))),
                                mapany(e -> esc(_views(e)), ex.args[2:end])...))), Base)
        else
            exprarray(ex.head, mapany(_views, ex.args))
        end
    end
end
```
  -/
  def viewsExpr (hooks : ViewsHooks) (head : String) (args : List ViewSyntax) : ViewResult ViewSyntax := do
    if head == "=" || head == ".=" then
      let lhs ← syntaxArg args 0
      let rewrittenLhs ←
        if isExpr lhs "ref" then do
          let rewritten ← (syntaxArgs lhs).mapM (viewsAny hooks)
          pure (.expr "ref" rewritten)
        else viewsAny hooks lhs
      let originalRhs ← syntaxArg args 1
      let rhs ← viewsAny hooks originalRhs
      pure (.expr head [rewrittenLhs, rhs])
    else if head == "ref" then
      let rewritten ← args.mapM (viewsAny hooks)
      pure (syntaxCall (.global "Base.maybeview") rewritten)
    else if head == "" then
      throw .boundsError
    else if endsInEquals head && args.isEmpty then
      throw .boundsError
    else if endsInEquals head && args.head?.any (fun lhs => isExpr lhs "ref") then
      let lhs ← syntaxArg args 0
      let lhsArgs := syntaxArgs lhs
      let indices := lhsArgs.drop 1
      let indexed ← prepareOpIndices indices
      let indexExpressions := indexed.map Prod.fst
      let sourceIndices := indexed.map Prod.snd
      let arrayVariable := ViewSyntax.symbol "a"
      let array ← syntaxArg lhsArgs 0
      let rewrittenArray ← viewsAny hooks array
      let rewrittenBindings ← (indexList 1 sourceIndices).mapM
        (fun (position, index) => do
          let rewritten ← viewsAny hooks index
          pure (.expr "=" [ViewSyntax.symbol ("i" ++ toString position), escapeSyntax rewritten]))
      let bindings := [.expr "=" [arrayVariable, escapeSyntax rewrittenArray]] ++ rewrittenBindings
      let assignmentHead := if startsInDot head then ".=" else "="
      let target := .expr "ref" (arrayVariable :: indexExpressions)
      let operation := ViewSyntax.symbol (dropLastChar head)
      let viewed := syntaxCall (.global "Base.maybeview") (arrayVariable :: indexExpressions)
      let rhs ← (args.drop 1).mapM (fun value => do
        let rewritten ← viewsAny hooks value
        pure (escapeSyntax rewritten))
      let operationCall := syntaxCall (escapeSyntax operation) (viewed :: rhs)
      let assignment := .expr assignmentHead [target, operationCall]
      let letExpression := .expr "let" [.expr "block" bindings, assignment]
      pure (.expr "hygienic-scope" [letExpression, .global "Base"])
    else
      let rewritten ← args.mapM (viewsAny hooks)
      pure (hooks.exprarray head rewritten)
  partial_fixpoint
end

/--
Julia source: base/views.jl:332-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro views(x)
    esc(_views(replace_ref_begin_end!(__module__, x)))
end
```
-/
def viewsMacro {Module : Type} (replaceHooks : ReplaceHooks Module) (rewriteHooks : ViewsHooks)
    (moduleValue : Module) (expression : ViewSyntax) : ViewResult ViewSyntax := do
  let expression ← replace_ref_begin_end! replaceHooks moduleValue expression
  let rewritten ← viewsAny rewriteHooks expression
  pure (escapeSyntax rewritten)

end JuliaLean.base.views
