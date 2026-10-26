import JuliaLean.MultidimCov.Model

open JuliaLean JuliaLean.MultidimCov

private def i (x : Int) : I64 := JInt.lit .i64 x
private def ax (first step : Int) (len : Nat) : Axis := { first := i first, step := i step, len }

#eval showCartesian [i 2, i (-1), i 5]
#eval makeCartesian 4 [i 7, i 8]
#eval cartesianNeg [i 2, i (-1), i 5]
#eval cartesianProduct [ax 2 2 3, ax 5 1 2]
#eval reverseAxes [ax 2 2 3, ax 5 1 2] [i 1]
#eval indexNdims [.scalar, .cartesian 2, .boolArray 3 [2, 3, 4]]
#eval indexDims [.scalar, .colon 4, .array [2, 3], .boolArray 2 [2, 2]]
#eval indexShape [.scalar, .colon 4, .array [2, 3], .boolArray 2 [2, 2]]
#eval collectLogicalIndex { mask := [true, true], cachedCount := 1 }
#eval collectLogicalIndex { mask := [true, false], cachedCount := 2 }
#eval diffRows [[i 1, i 4, i 9], [i 2, i 8, i 18]] 2
#eval tryBoolConversion (i 2)
#eval permutedimsStrided [ax 2 1 2, ax 1 1 3] [1, 0]
#eval viewIndexing [.slice (ax 1 1 3), .range (ax 2 1 2), .scalar (i 1)]
#eval subAxes [.scalar (i 2), .slice (ax 1 1 3), .array [ax 1 1 2] [i 1, i 2]]
#eval eachsliceModel [ax 1 1 2, ax 1 1 3] [i 4] false
