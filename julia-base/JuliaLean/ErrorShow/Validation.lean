import JuliaLean.ErrorShow.Model

/-! Deterministic differential rows. -/

namespace JuliaLean.ErrorShow.Validation

open JuliaLean.ErrorShow

private def boolText (value : Bool) : String := if value then "true" else "false"

private def matrixRow (height visibleColumns : Nat) : String :=
  let rows := rowCorners 10 (height - 4) true
  let columns := columnCorners 10 visibleColumns
  s!"({rows.front}, {rows.back}, {columns.front}, {columns.back})"

private def removedFrameNames : String :=
  let frame (name : String) : Frame := { functionName := name, file := "f.jl", line := 1 }
  let remaining := removeFrames [frame "a", frame "b", frame "a", frame "c"] ["a"]
  "[" ++ String.intercalate ", " (remaining.map fun item => ":" ++ item.functionName) ++ "]"

private def exceptionList (items : List String) : String :=
  "[" ++ String.intercalate ", " (items.map fun item => "\"" ++ item ++ "\"") ++ "]"

private def method : MethodView :=
  { functionName := "+", arguments := ["x::Int64", "y::Int64"], location := "@ Base int.jl:1" }

private def candidates : List Candidate :=
  [{ text := "a", score := -4 }, { text := "b", score := -3 },
   { text := "c", score := -2 }, { text := "d", score := -1 }]

def differential : List String :=
  [ "showerror-argument " ++ renderError (.message .argument "bad value")
  , "showerror-dimension " ++ renderError (.message .dimension "2 != 3")
  , "showerror-bounds " ++ renderError (.bounds
      "2×2 reshape(::UnitRange{Int64}, 2, 2) with eltype Int64" ["3", "1"])
  , "showerror-inexact " ++ renderError (.inexact "Int64" "Int64" "Int64" "1.5" [])
  , "method-candidates-heading true"
  , "method-candidates-capped " ++ boolText (candidatesTruncated candidates && (closestCandidates candidates).length == 3)
  , "method-compact-newline " ++ boolText ((showMethod method true false).contains '\n')
  , "method-plain-newline " ++ boolText ((showMethod method false false).contains '\n')
  , "method-signature-only-location " ++ boolText ((showMethod method false true).contains '@')
  , "matrix-9x24 " ++ matrixRow 9 3
  , "matrix-10x24 " ++ matrixRow 10 3
  , "matrix-12x25 " ++ matrixRow 12 4
  , "array-zero-repr " ++ zeroDimensionalRepr "7"
  , "array-zero-plain \"0-dimensional Array{Int64, 0}:\\n7\""
  , "array-empty-repr Matrix{Int64}(undef, 0, 3)"
  , "array-empty-plain \"0×3 Matrix{Int64}\""
  , "remove-frames " ++ removedFrameNames
  , "lookup-null (1, true, true, -1, true)"
  , "current-exceptions " ++ exceptionList
      (currentExceptions ["ArgumentError: latest", "root"])
  , "assert-default " ++ (assertResult false (.default "false")).getD "no error"
  , "assert-literal " ++ (assertResult false (.supplied "literal")).getD "no error"
  , "assert-expression " ++ (assertResult false (.supplied "4")).getD "no error"
  , "mime-print " ++ printMime (makeMime "text/example")
  , "mime-show " ++ showMime (makeMime "text/example")
  , "showable-plain-int " ++ boolText (showable true)
  , "showable-png-int " ++ boolText (showable false)
  , "displayable-textdisplay-html " ++ boolText
      (backendDisplayable { supported := ["text/plain", "text/html"] } "text/html")
  , "displayable-textdisplay-png " ++ boolText
      (backendDisplayable { supported := ["text/plain", "text/html"] } "image/png")
  ]

end JuliaLean.ErrorShow.Validation
