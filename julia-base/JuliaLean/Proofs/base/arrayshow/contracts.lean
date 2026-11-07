import JuliaLean.base.arrayshow


namespace JuliaLean.ErrorShow


def MatrixColumnAlignment : Prop := ∀ column cell : Alignment,
  cell.left ≤ column.left → cell.right ≤ column.right →
    paddedWidth column cell = column.left + column.right

def MatrixCornerTruncation : Prop :=
  (∀ rows screenRows : Nat, screenRows < rows →
    rowCorners rows screenRows true =
      { front := screenRows / 2, back := (screenRows - 1) / 2, truncated := true }) ∧
  (∀ columns visible : Nat, visible < columns →
    columnCorners columns visible =
      { front := (visible + 1) / 2, back := visible / 2, truncated := true })

def PrintArrayRoutes : Prop :=
  (∀ compact : Bool, ∀ screenRows : Nat,
    arrayRoute 0 1 false false compact false screenRows = .zeroDimensional) ∧
  (∀ rank rows screenRows : Nat, ∀ compact limited : Bool,
    arrayRoute rank rows true true compact limited screenRows = .twoArgumentShow) ∧
  (∀ rank rows screenRows : Nat, ∀ limited : Bool,
    arrayRoute rank rows false true true limited screenRows = .twoArgumentShow) ∧
  (∀ rank rows screenRows : Nat,
    arrayRoute rank rows false true false false screenRows = .summaryOnly)

theorem matrixColumnAlignment_proven : MatrixColumnAlignment := by
  intro column cell left right
  simp [paddedWidth, Nat.sub_add_cancel left]
  omega

theorem matrixCornerTruncation_proven : MatrixCornerTruncation := by
  constructor
  · intro rows screenRows truncated
    simp [rowCorners, truncated]
  · intro columns visible truncated
    simp [columnCorners, truncated]

theorem printArrayRoutes_proven : PrintArrayRoutes := by
  constructor
  · intro compact screenRows
    simp [arrayRoute]
  constructor
  · intro rank rows screenRows compact limited
    simp [arrayRoute]
  constructor
  · intro rank rows screenRows limited
    simp [arrayRoute]
  · intro rank rows screenRows
    simp [arrayRoute]

end JuliaLean.ErrorShow
