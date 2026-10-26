import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.SyntaxExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def nothing (rt : Runtime) : M Value := call0 rt "nothing"

def m1297 (rt : Runtime) (args : Value) : M Value := call1 rt "Base.maybeview:slurp" args
def P1297 : Prop := ∀ rt args, m1297 rt args = call1 rt "Base.maybeview:slurp" args
theorem p1297 : P1297 := by simp [P1297, m1297]

def m1304 (rt : Runtime) (_x : Value) : M Value := call0 rt "false"
def P1304 : Prop := ∀ rt x, m1304 rt x = call0 rt "false"
theorem p1304 : P1304 := by simp [P1304, m1304]

def m1306 (rt : Runtime) (x : Value) : M Value := do
  let isop ← call1 rt "isoperator" x
  let left ← if !rt.truth isop then call0 rt "true" else
    let s ← call1 rt "string" x
    let first ← call1 rt "first" s
    call2 rt "!=" first (← call0 rt "Char:.")
  let dotdot ← call0 rt "Symbol:.."
  let left ← if rt.truth left then pure left else call2 rt "===" x dotdot
  if !rt.truth left then call0 rt "false" else call2 rt "!==" x (← call0 rt "Symbol::")
def P1306 : Prop := ∀ rt x, m1306 rt x = do
  let isop ← call1 rt "isoperator" x
  let left ← if !rt.truth isop then call0 rt "true" else
    let s ← call1 rt "string" x
    let first ← call1 rt "first" s
    call2 rt "!=" first (← call0 rt "Char:.")
  let dotdot ← call0 rt "Symbol:.."
  let left ← if rt.truth left then pure left else call2 rt "===" x dotdot
  if !rt.truth left then call0 rt "false" else call2 rt "!==" x (← call0 rt "Symbol::")
theorem p1306 : P1306 := by simp [P1306, m1306]

def m1307 (rt : Runtime) (x : Value) : M Value := do
  let head ← call1 rt "getfield:head" x
  call2 rt "!==" head (← call0 rt "Symbol:$")
def P1307 : Prop := ∀ rt x, m1307 rt x = do
  let head ← call1 rt "getfield:head" x
  call2 rt "!==" head (← call0 rt "Symbol:$")
theorem p1307 : P1307 := by simp [P1307, m1307]

def m1308 (_rt : Runtime) (x : Value) : M Value := pure x
def P1308 : Prop := ∀ rt x, m1308 rt x = pure x
theorem p1308 : P1308 := by simp [P1308, m1308]

def m1309 (rt : Runtime) (x : Value) : M Value := do
  let head ← call1 rt "getfield:head" x
  if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:.=")) then
    let args ← call1 rt "getfield:args" x
    rt.call "Expr:slurp" [(← call0 rt "Symbol:="), args]
  else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:block")) then
    let args ← call1 rt "getfield:args" x
    let args ← call2 rt "Base.mapany" (← call0 rt "undot:function") args
    rt.call "Expr:slurp" [head, args]
  else pure x
def P1309 : Prop := ∀ rt x, m1309 rt x = do
  let head ← call1 rt "getfield:head" x
  if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:.=")) then
    let args ← call1 rt "getfield:args" x
    rt.call "Expr:slurp" [(← call0 rt "Symbol:="), args]
  else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:block")) then
    let args ← call1 rt "getfield:args" x
    let args ← call2 rt "Base.mapany" (← call0 rt "undot:function") args
    rt.call "Expr:slurp" [head, args]
  else pure x
theorem p1309 : P1309 := by simp [P1309, m1309]

def m1318 (_rt : Runtime) (x : Value) : M Value := pure x
def P1318 : Prop := ∀ rt x, m1318 rt x = pure x
theorem p1318 : P1318 := by simp [P1318, m1318]

def program1319 (rt : Runtime) (x : Value) : M Value := do
  let args ← call1 rt "getfield:args" x
  let dotargs ← call2 rt "Base.mapany" (← call0 rt "__dot__:function") args
  let head ← call1 rt "getfield:head" x
  if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:call")) then
    let f ← call2 rt "getindex" args (← call0 rt "Int:1")
    if rt.truth (← call1 rt "dottable" f) then
      let df ← call2 rt "getindex" dotargs (← call0 rt "Int:1")
      let rest ← call2 rt "getindex:2:end" dotargs (← call0 rt "range:2:end")
      let tuple ← call1 rt "Expr:tuple" rest
      rt.call "Expr" [(← call0 rt "Symbol:."), df, tuple]
    else rt.call "Expr:slurp" [head, dotargs]
  else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:comparison")) then
    rt.call "Expr:comparison-dotted-operators" [dotargs]
  else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:$")) then
    call2 rt "getindex" args (← call0 rt "Int:1")
  else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:let")) then
    let lhs ← call2 rt "getindex" dotargs (← call0 rt "Int:1")
    let lhs ← call1 rt "undot" lhs
    let body ← call2 rt "getindex" dotargs (← call0 rt "Int:2")
    rt.call "Expr" [head, lhs, body]
  else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:for")) then
    let lhs ← call2 rt "getindex" dotargs (← call0 rt "Int:1")
    let lhs ← call1 rt "undot" lhs
    let body ← call2 rt "getindex" dotargs (← call0 rt "Int:2")
    rt.call "Expr" [head, lhs, body]
  else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:generator")) ||
      rt.truth (← call2 rt "===" head (← call0 rt "Symbol:filter")) then
    let first ← call2 rt "getindex" dotargs (← call0 rt "Int:1")
    let rest ← call2 rt "getindex:2:end" dotargs (← call0 rt "range:2:end")
    let rest ← call2 rt "map" (← call0 rt "undot:function") rest
    rt.call "Expr:first-slurp" [head, first, rest]
  else
    let assignment ← call2 rt "===" head (← call0 rt "Symbol:=" )
    let functionHead ← call2 rt "===" head (← call0 rt "Symbol:function")
    let macroHead ← call2 rt "===" head (← call0 rt "Symbol:macro")
    let isDefinition ← if rt.truth assignment || rt.truth functionHead || rt.truth macroHead then
      let first ← call2 rt "getindex" args (← call0 rt "Int:1")
      rt.call "Meta.isexpr" [first, (← call0 rt "Symbol:call")]
    else call0 rt "false"
    if rt.truth isDefinition then
      let lhs ← call2 rt "getindex" args (← call0 rt "Int:1")
      let body ← call2 rt "getindex" dotargs (← call0 rt "Int:2")
      rt.call "Expr" [head, lhs, body]
    else if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:<:")) ||
        rt.truth (← call2 rt "===" head (← call0 rt "Symbol:>:")) then
      let op ← if rt.truth (← call2 rt "===" head (← call0 rt "Symbol:<:")) then
        call0 rt "Symbol:.<:" else call0 rt "Symbol:.>:"
      rt.call "Expr:call-slurp" [op, dotargs]
    else
      let name ← call1 rt "String" head
      let last ← call1 rt "last" name
      let first ← call1 rt "first" name
      let assignmentLike ← if rt.truth (← call2 rt "==" last (← call0 rt "Char:=")) then
        call2 rt "!=" first (← call0 rt "Char:.") else call0 rt "false"
      let andHead ← call2 rt "==" name (← call0 rt "String:&&")
      let orHead ← call2 rt "==" name (← call0 rt "String:||")
      if rt.truth assignmentLike || rt.truth andHead || rt.truth orHead then
        let dotted ← call2 rt "string:*" (← call0 rt "String:.") name
        let dotted ← call1 rt "Symbol" dotted
        rt.call "Expr:slurp" [dotted, dotargs]
      else rt.call "Expr:slurp" [head, dotargs]
def m1319 (rt : Runtime) (x : Value) : M Value := program1319 rt x
def P1319 : Prop := ∀ rt x, m1319 rt x = program1319 rt x
theorem p1319 : P1319 := by simp [P1319, m1319]

def m1390 (rt : Runtime) (x : Value) : M Value := do
  let dotted ← call1 rt "__dot__" x
  call1 rt "esc" dotted
def P1390 : Prop := ∀ rt x, m1390 rt x = do
  let dotted ← call1 rt "__dot__" x
  call1 rt "esc" dotted
theorem p1390 : P1390 := by simp [P1390, m1390]

def m1394 (rt : Runtime) (f args kwargs : Value) : M Value := do
  if rt.truth (← call1 rt "isempty" kwargs) then rt.call "broadcasted:slurp" [f, args] else
    let closure ← rt.call "closure:(args...)->f(args...;kwargs...)" [f, kwargs]
    rt.call "broadcasted:slurp" [closure, args]
def P1394 : Prop := ∀ rt f args kwargs, m1394 rt f args kwargs = do
  if rt.truth (← call1 rt "isempty" kwargs) then rt.call "broadcasted:slurp" [f, args] else
    let closure ← rt.call "closure:(args...)->f(args...;kwargs...)" [f, kwargs]
    rt.call "broadcasted:slurp" [closure, args]
theorem p1394 : P1394 := by simp [P1394, m1394]

def m1401 (rt : Runtime) (f args : Value) : M Value := do
  let mapped ← call2 rt "map" (← call0 rt "broadcastable:function") args
  let style ← call1 rt "combine_styles:slurp" mapped
  rt.call "broadcasted:style-slurp" [style, f, mapped]
def P1401 : Prop := ∀ rt f args, m1401 rt f args = do
  let mapped ← call2 rt "map" (← call0 rt "broadcastable:function") args
  let style ← call1 rt "combine_styles:slurp" mapped
  rt.call "broadcasted:style-slurp" [style, f, mapped]
theorem p1401 : P1401 := by simp [P1401, m1401]

def m1409 (rt : Runtime) (f arg1 args : Value) : M Value := do
  let arg1 ← call1 rt "broadcastable" arg1
  let mapped ← call2 rt "map" (← call0 rt "broadcastable:function") args
  let style ← rt.call "combine_styles:head-slurp" [arg1, mapped]
  rt.call "broadcasted:style-head-slurp" [style, f, arg1, mapped]
def P1409 : Prop := ∀ rt f arg1 args, m1409 rt f arg1 args = do
  let arg1 ← call1 rt "broadcastable" arg1
  let mapped ← call2 rt "map" (← call0 rt "broadcastable:function") args
  let style ← rt.call "combine_styles:head-slurp" [arg1, mapped]
  rt.call "broadcasted:style-head-slurp" [style, f, arg1, mapped]
theorem p1409 : P1409 := by simp [P1409, m1409]

def m1414 (rt : Runtime) (f arg1 arg2 args : Value) : M Value := do
  let arg1 ← call1 rt "broadcastable" arg1
  let arg2 ← call1 rt "broadcastable" arg2
  let mapped ← call2 rt "map" (← call0 rt "broadcastable:function") args
  let style ← rt.call "combine_styles:two-slurp" [arg1, arg2, mapped]
  rt.call "broadcasted:style-two-slurp" [style, f, arg1, arg2, mapped]
def P1414 : Prop := ∀ rt f arg1 arg2 args, m1414 rt f arg1 arg2 args = do
  let arg1 ← call1 rt "broadcastable" arg1
  let arg2 ← call1 rt "broadcastable" arg2
  let mapped ← call2 rt "map" (← call0 rt "broadcastable:function") args
  let style ← rt.call "combine_styles:two-slurp" [arg1, arg2, mapped]
  rt.call "broadcasted:style-two-slurp" [style, f, arg1, arg2, mapped]
theorem p1414 : P1414 := by simp [P1414, m1414]

def m1420 (rt : Runtime) (style f args : Value) : M Value :=
  rt.call "Broadcasted" [style, f, args]
def P1420 : Prop := ∀ rt style f args, m1420 rt style f args = rt.call "Broadcasted" [style, f, args]
theorem p1420 : P1420 := by simp [P1420, m1420]

def m1452 (rt : Runtime) (op x kwargs : Value) : M Value := do
  let f ← call1 rt "getfield:f" op
  rt.call "broadcast-call:slurp-keywords" [f, x, kwargs]
def P1452 : Prop := ∀ rt op x kwargs, m1452 rt op x kwargs = do
  let f ← call1 rt "getfield:f" op
  rt.call "broadcast-call:slurp-keywords" [f, x, kwargs]
theorem p1452 : P1452 := by simp [P1452, m1452]

def m1454 (rt : Runtime) (io op : Value) : M Value := do
  let _ ← call2 rt "print" io (← call0 rt "BroadcastFunction:type")
  let _ ← call2 rt "print" io (← call0 rt "Char:(")
  let f ← call1 rt "getfield:f" op
  let _ ← call2 rt "show" io f
  let _ ← call2 rt "print" io (← call0 rt "Char:)")
  nothing rt
def P1454 : Prop := ∀ rt io op, m1454 rt io op = do
  let _ ← call2 rt "print" io (← call0 rt "BroadcastFunction:type")
  let _ ← call2 rt "print" io (← call0 rt "Char:(")
  let f ← call1 rt "getfield:f" op
  let _ ← call2 rt "show" io f
  let _ ← call2 rt "print" io (← call0 rt "Char:)")
  nothing rt
theorem p1454 : P1454 := by simp [P1454, m1454, nothing]

def m1460 (rt : Runtime) (io op : Value) : M Value := call2 rt "show" io op
def P1460 : Prop := ∀ rt io op, m1460 rt io op = call2 rt "show" io op
theorem p1460 : P1460 := by simp [P1460, m1460]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement := statement,
    source := s!"base/broadcast.jl:{line}; exact syntax or wrapper equation",
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry 1297 "dotview(args...)" "Generic dotview delegates to maybeview." ``P1297 ``p1297,
  entry 1304 "dottable(x)" "The fallback is false." ``P1304 ``p1304,
  entry 1306 "dottable(::Symbol)" "Symbol dottability follows operator, dot-prefix, .. and colon checks in source order." ``P1306 ``p1306,
  entry 1307 "dottable(::Expr)" "Only interpolation expressions are not dottable." ``P1307 ``p1307,
  entry 1308 "undot(x)" "The fallback returns x." ``P1308 ``p1308,
  entry 1309 "undot(::Expr)" "Dot assignment is rewritten, blocks recurse, and other expressions pass through." ``P1309 ``p1309,
  entry 1318 "__dot__(x)" "The non-expression fallback returns x." ``P1318 ``p1318,
  entry 1319 "__dot__(::Expr)" "Expression dotting recursively maps arguments and executes every source head branch in order." ``P1319 ``p1319,
  entry 1390 "@__dot__(x)" "The macro dots then escapes its input." ``P1390 ``p1390,
  entry 1394 "broadcasted_kwsyntax" "Keyword syntax preserves f without kwargs and otherwise captures kwargs in a closure." ``P1394 ``p1394,
  entry 1401 "broadcasted(f,args...)" "Generic broadcastability mapping precedes style combination and construction." ``P1401 ``p1401,
  entry 1409 "broadcasted(f,arg1,args...)" "The first argument is converted before mapped trailing arguments and style combination." ``P1409 ``p1409,
  entry 1414 "broadcasted(f,arg1,arg2,args...)" "Two leading arguments are converted in order before the trailing map and construction." ``P1414 ``p1414,
  entry 1420 "broadcasted(style,f,args...)" "Explicit-style broadcast constructs Broadcasted directly." ``P1420 ``p1420,
  entry 1452 "(::BroadcastFunction)(x...;kwargs...)" "BroadcastFunction delegates dotted application to its stored f." ``P1452 ``p1452,
  entry 1454 "show(::BroadcastFunction)" "Showing prints the wrapper, function and delimiter in order, then nothing." ``P1454 ``p1454,
  entry 1460 "show(::MIME,::BroadcastFunction)" "Plain-text show delegates to show(io,op)." ``P1460 ``p1460
]

end JuliaLean.BroadcastCov.SyntaxExact
