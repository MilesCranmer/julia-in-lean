import JuliaLean.Core

/-!
# Model of `base/osutils.jl`

`@static` remains untranslated because it evaluates and rewrites Julia syntax during macro expansion.
-/

namespace JuliaLean.base.osutils

-- This macro invokes Julia's expression evaluator at expansion time.
-- UNTRANSLATED
-- Source: base/osutils.jl:1-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     @static
-- 
-- Partially evaluate an expression at macro expansion time.
-- 
-- This is useful in cases where a construct would be invalid in some cases, such as a `ccall`
-- to an os-dependent function, or macros defined in packages that are not imported.
-- 
-- `@static` requires a conditional. The conditional can be in an `if` statement, a ternary
-- operator, or `&&`\`||`. The conditional is evaluated by recursively expanding macros,
-- lowering and executing the resulting expressions. Then, the matching branch (if any) is
-- returned. All the other branches of the conditional are deleted before they are
-- macro-expanded (and lowered or executed).
-- 
-- # Example
-- 
-- Suppose we want to parse an expression `expr` that is valid only on macOS. We could solve
-- this problem using `@static` with `@static if Sys.isapple() expr end`. In case we had
-- `expr_apple` for macOS and `expr_others` for the other operating systems, the solution with
-- `@static` would be `@static Sys.isapple() ? expr_apple : expr_others`.
-- """
-- macro static(ex)
--     if isa(ex, Expr)
--         @label loop
--         hd = ex.head
--         if hd ∈ (:if, :elseif, :&&, :||)
--             cond = Core.eval(__module__, ex.args[1])::Bool
--             if xor(cond, hd === :||)
--                 return esc(ex.args[2])
--             elseif length(ex.args) == 3
--                 br = ex.args[3]
--                 if br isa Expr && br.head === :elseif
--                     ex = br
--                     @goto loop
--                 else
--                     return esc(ex.args[3])
--                 end
--             elseif hd ∈ (:if, :elseif)
--                 return nothing
--             else
--                 return cond
--             end
--         end
--     end
--     throw(ArgumentError("invalid @static macro"))
-- end
-- /Source
end JuliaLean.base.osutils

namespace JuliaLean.MiscCov.Static

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

end JuliaLean.MiscCov.Static
