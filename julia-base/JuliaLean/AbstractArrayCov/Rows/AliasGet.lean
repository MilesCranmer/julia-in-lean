import JuliaLean.AbstractArrayCov.Rows.Index

/-! Method-specific models for `base/abstractarray.jl:1548-1694`. -/

namespace JuliaLean.AbstractArrayCov.Rows.AliasGet

open JuliaLean
open JuliaLean.Registry

/-- `parent(a::AbstractArray)`, line 1548. -/
def method1548 (a : α) : α := a
def Property1548 : Prop := ∀ (α : Type) (a : α), method1548 a = a
theorem property1548 : Property1548 := by unfold Property1548; intros; rfl

/-- Array `unalias`, line 1566. -/
def method1566 (mightalias : δ → α → Bool) (copy : α → α) (dest : δ) (a : α) : α :=
  if mightalias dest a then copy a else a
def Property1566 : Prop := ∀ (δ α : Type) (mightalias : δ → α → Bool)
    (copy : α → α) dest a,
  method1566 mightalias copy dest a = if mightalias dest a then copy a else a
theorem property1566 : Property1566 := by unfold Property1566; intros; rfl

/-- Range `unalias`, line 1567. -/
def method1567 (_dest : δ) (a : α) : α := a
def Property1567 : Prop := ∀ (δ α : Type) (dest : δ) (a : α), method1567 dest a = a
theorem property1567 : Property1567 := by unfold Property1567; intros; rfl

/-- Generic `unalias`, line 1568. -/
def method1568 (_dest : δ) (a : α) : α := a
def Property1568 : Prop := ∀ (δ α : Type) (dest : δ) (a : α), method1568 dest a = a
theorem property1568 : Property1568 := by unfold Property1568; intros; rfl

/-- Array `unaliascopy`, line 1582. -/
def method1582 (copy : α → β) (a : α) : β := copy a
def Property1582 : Prop := ∀ (α β : Type) (copy : α → β) a,
  method1582 copy a = copy a
theorem property1582 : Property1582 := by unfold Property1582; intros; rfl

/-- AbstractArray `unaliascopy`, line 1583. -/
def method1583 (copy : α → β) (finish : α → β → Jl α) (a : α) : Jl α :=
  finish a (copy a)
def Property1583 : Prop := ∀ (α β : Type) (copy : α → β)
    (finish : α → β → Jl α) a,
  method1583 copy finish a = finish a (copy a)
theorem property1583 : Property1583 := by unfold Property1583; intros; rfl

/-- Same-type `_unaliascopy`, line 1584. -/
def method1584 (_a : α) (copy : α) : α := copy
def Property1584 : Prop := ∀ (α : Type) a copy, method1584 (α := α) a copy = copy
theorem property1584 : Property1584 := by unfold Property1584; intros; rfl

/-- Wrong-type `_unaliascopy`, lines 1585-1592. -/
def method1585 (arrayType copyType : String) : Jl α :=
  .error (.argumentError ("copy(::" ++ arrayType ++ ") returns " ++ copyType))
def Property1585 : Prop := ∀ (α : Type) arrayType copyType,
  (method1585 arrayType copyType : Jl α) =
    .error (.argumentError ("copy(::" ++ arrayType ++ ") returns " ++ copyType))
theorem property1585 : Property1585 := by unfold Property1585; intros; rfl

/-- Generic `unaliascopy`, line 1593. -/
def method1593 (a : α) : α := a
def Property1593 : Prop := ∀ (α : Type) (a : α), method1593 a = a
theorem property1593 : Property1593 := by unfold Property1593; intros; rfl

/-- Array `mightalias`, line 1603, preserving short-circuit order. -/
def method1603 (isbits : α → Bool) (isempty : α → Bool) (dataids : α → List Nat)
    (disjoint : List Nat → List Nat → Bool) (a b : α) : Bool :=
  !isbits a && !isbits b && !isempty a && !isempty b && !disjoint (dataids a) (dataids b)
def Property1603 : Prop := ∀ (α : Type) (isbits isempty : α → Bool)
    (dataids : α → List Nat) disjoint a b,
  method1603 isbits isempty dataids disjoint a b =
    (!isbits a && !isbits b && !isempty a && !isempty b && !disjoint (dataids a) (dataids b))
theorem property1603 : Property1603 := by unfold Property1603; intros; rfl

/-- Generic `mightalias`, line 1604. -/
def method1604 : Bool := false
def Property1604 : Prop := ∀ (_x _y : Nat), method1604 = false
theorem property1604 : Property1604 := by unfold Property1604; intros; rfl

/-- Empty/empty `_isdisjoint`, line 1606. -/
def method1606 : Bool := true
def Property1606 : Prop := ∀ _empty : Unit, method1606 = true
theorem property1606 : Property1606 := by unfold Property1606; intros; rfl

/-- Empty/singleton `_isdisjoint`, line 1607. -/
def method1607 (_b : Nat) : Bool := true
def Property1607 : Prop := ∀ b, method1607 b = true
theorem property1607 : Property1607 := by unfold Property1607; intros; rfl

/-- Empty/tuple `_isdisjoint`, line 1608. -/
def method1608 (_bs : List Nat) : Bool := true
def Property1608 : Prop := ∀ bs, method1608 bs = true
theorem property1608 : Property1608 := by unfold Property1608; intros; rfl

/-- Singleton/empty `_isdisjoint`, line 1609. -/
def method1609 (_a : Nat) : Bool := true
def Property1609 : Prop := ∀ a, method1609 a = true
theorem property1609 : Property1609 := by unfold Property1609; intros; rfl

/-- Singleton/singleton `_isdisjoint`, line 1610. -/
def method1610 (a b : Nat) : Bool := a != b
def Property1610 : Prop := ∀ a b, method1610 a b = (a != b)
theorem property1610 : Property1610 := by unfold Property1610; intros; rfl

/-- Singleton/tuple `_isdisjoint`, line 1611. -/
def method1611 (a : Nat) (bs : List Nat) : Bool := !bs.contains a
def Property1611 : Prop := ∀ a bs, method1611 a bs = !bs.contains a
theorem property1611 : Property1611 := by unfold Property1611; intros; rfl

/-- Tuple/empty `_isdisjoint`, line 1612. -/
def method1612 (_as : List Nat) : Bool := true
def Property1612 : Prop := ∀ as, method1612 as = true
theorem property1612 : Property1612 := by unfold Property1612; intros; rfl

/-- Tuple/singleton `_isdisjoint`, line 1613. -/
def method1613 (as : List Nat) (b : Nat) : Bool := !as.contains b
def Property1613 : Prop := ∀ as b, method1613 as b = !as.contains b
theorem property1613 : Property1613 := by unfold Property1613; intros; rfl

/-- Tuple/tuple recursive `_isdisjoint`, line 1614. -/
def method1614 (recurse : List Nat → List Nat → Bool) (as bs : List Nat) : Bool :=
  match as with
  | [] => true
  | a :: rest => !bs.contains a && recurse rest bs
def Property1614 : Prop := ∀ recurse as bs,
  method1614 recurse as bs = match as with
    | [] => true
    | a :: rest => !bs.contains a && recurse rest bs
theorem property1614 : Property1614 := by
  unfold Property1614
  intro recurse as bs
  cases as <;> rfl

/-- AbstractArray `dataids`, line 1626. -/
def method1626 (objectid : α → Nat) (a : α) : List Nat := [objectid a]
def Property1626 : Prop := ∀ (α : Type) (objectid : α → Nat) a,
  method1626 objectid a = [objectid a]
theorem property1626 : Property1626 := by unfold Property1626; intros; rfl

/-- Memory `dataids`, line 1627. -/
def method1627 (pointer : α → Nat) (a : α) : List Nat := [pointer a]
def Property1627 : Prop := ∀ (α : Type) (pointer : α → Nat) a,
  method1627 pointer a = [pointer a]
theorem property1627 : Property1627 := by unfold Property1627; intros; rfl

/-- Array `dataids`, line 1628. -/
def method1628 (memory : α → β) (dataids : β → List Nat) (a : α) : List Nat :=
  dataids (memory a)
def Property1628 : Prop := ∀ (α β : Type) (memory : α → β)
    (dataids : β → List Nat) a,
  method1628 memory dataids a = dataids (memory a)
theorem property1628 : Property1628 := by unfold Property1628; intros; rfl

/-- Range `dataids`, line 1629. -/
def method1629 : List Nat := []
def Property1629 : Prop := ∀ _range : Unit, method1629 = []
theorem property1629 : Property1629 := by unfold Property1629; intros; rfl

/-- Generic `dataids`, line 1630. -/
def method1630 : List Nat := []
def Property1630 : Prop := ∀ _value : Nat, method1630 = []
theorem property1630 : Property1630 := by unfold Property1630; intros; rfl

def getDefault (check : Bool) (get : Unit → α) (default : Unit → α) : α :=
  if check then get () else default ()

/-- Scalar defaulted `get`, line 1637. -/
def method1637 (check : α → Int → Bool) (get : α → Int → β)
    (a : α) (i : Int) (default : β) : β :=
  if check a i then get a i else default
def Property1637 : Prop := ∀ (α β : Type) (check : α → Int → Bool)
    (get : α → Int → β) a i default,
  method1637 check get a i default = if check a i then get a i else default
theorem property1637 : Property1637 := by unfold Property1637; intros; rfl

/-- Zero-index defaulted `get`, line 1638. -/
def method1638 (check : α → Bool) (get : α → β) (a : α) (default : β) : β :=
  if check a then get a else default
def Property1638 : Prop := ∀ (α β : Type) (check : α → Bool) (get : α → β) a default,
  method1638 check get a default = if check a then get a else default
theorem property1638 : Property1638 := by unfold Property1638; intros; rfl

/-- Dim-tuple defaulted `get`, line 1639. -/
def method1639 (check : α → List Int → Bool) (get : α → List Int → β)
    (a : α) (indices : List Int) (default : β) : β :=
  if check a indices then get a indices else default
def Property1639 : Prop := ∀ (α β : Type) (check : α → List Int → Bool)
    (get : α → List Int → β) a indices default,
  method1639 check get a indices default = if check a indices then get a indices else default
theorem property1639 : Property1639 := by unfold Property1639; intros; rfl

/-- Callable scalar default `get`, line 1640. -/
def method1640 (check : α → Int → Bool) (get : α → Int → β)
    (fallback : Unit → β) (a : α) (i : Int) : β :=
  if check a i then get a i else fallback ()
def Property1640 : Prop := ∀ (α β : Type) (check : α → Int → Bool)
    (get : α → Int → β) fallback a i,
  method1640 check get fallback a i = if check a i then get a i else fallback ()
theorem property1640 : Property1640 := by unfold Property1640; intros; rfl

/-- Callable zero-index default `get`, line 1641. -/
def method1641 (check : α → Bool) (get : α → β) (fallback : Unit → β) (a : α) : β :=
  if check a then get a else fallback ()
def Property1641 : Prop := ∀ (α β : Type) (check : α → Bool)
    (get : α → β) fallback a,
  method1641 check get fallback a = if check a then get a else fallback ()
theorem property1641 : Property1641 := by unfold Property1641; intros; rfl

/-- Callable dim-tuple default `get`, line 1642. -/
def method1642 (check : α → List Int → Bool) (get : α → List Int → β)
    (fallback : Unit → β) (a : α) (indices : List Int) : β :=
  if check a indices then get a indices else fallback ()
def Property1642 : Prop := ∀ (α β : Type) (check : α → List Int → Bool)
    (get : α → List Int → β) fallback a indices,
  method1642 check get fallback a indices =
    if check a indices then get a indices else fallback ()
theorem property1642 : Property1642 := by unfold Property1642; intros; rfl

/-- Vector-index `get!`, lines 1644-1652. -/
def method1644 (findValid : β → List Int) (copySelected : δ → List Int → Jl δ)
    (fillRange : δ → Int → Int → α → Jl δ) (x : δ) (requested : β) (default : α)
    (firstX lastX : Int) : Jl δ := do
  let validPositions := findValid requested
  let x ← copySelected x validPositions
  let firstValid := validPositions.head?.getD (lastX + 1)
  let lastValid := validPositions.getLast?.getD (firstX - 1)
  let x ← fillRange x firstX (firstValid - 1) default
  fillRange x (lastValid + 1) lastX default
def Property1644 : Prop := ∀ (δ α β : Type) (findValid : β → List Int)
    (copySelected : δ → List Int → Jl δ) (fillRange : δ → Int → Int → α → Jl δ)
    x requested default firstX lastX,
  method1644 findValid copySelected fillRange x requested default firstX lastX = do
    let positions := findValid requested
    let x ← copySelected x positions
    let firstValid := positions.head?.getD (lastX + 1)
    let lastValid := positions.getLast?.getD (firstX - 1)
    let x ← fillRange x firstX (firstValid - 1) default
    fillRange x (lastValid + 1) lastX default
theorem property1644 : Property1644 := by unfold Property1644; intros; rfl

/-- Linear array `get!`, lines 1653-1660. -/
def method1653 (findValid : β → List Int) (copySelected : δ → List Int → Jl δ)
    (fillView : δ → Int → Int → α → Jl δ) (x : δ) (requested : β)
    (default : α) (lengthX : Int) : Jl δ := do
  let validPositions := findValid requested
  let x ← copySelected x validPositions
  let firstValid := validPositions.head?.getD (lengthX + 1)
  let lastValid := validPositions.getLast?.getD 0
  let x ← fillView x 1 (firstValid - 1) default
  fillView x (lastValid + 1) lengthX default
def Property1653 : Prop := ∀ (δ α β : Type) (findValid : β → List Int)
    (copySelected : δ → List Int → Jl δ) (fillView : δ → Int → Int → α → Jl δ)
    x requested default lengthX,
  method1653 findValid copySelected fillView x requested default lengthX = do
    let positions := findValid requested
    let x ← copySelected x positions
    let firstValid := positions.head?.getD (lengthX + 1)
    let lastValid := positions.getLast?.getD 0
    let x ← fillView x 1 (firstValid - 1) default
    fillView x (lastValid + 1) lengthX default
theorem property1653 : Property1653 := by unfold Property1653; intros; rfl

/-- Range defaulted `get`, line 1662. -/
def method1662 (typeof : α → τ) (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) (a : δ) (indices : ι) (default : α) : γ :=
  getBang (similar a (typeof default) (shape indices)) a indices default
def Property1662 : Prop := ∀ (α τ ι σ δ β γ : Type) (typeof : α → τ)
    (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) a indices default,
  method1662 typeof shape similar getBang a indices default =
    getBang (similar a (typeof default) (shape indices)) a indices default
theorem property1662 : Property1662 := by unfold Property1662; intros; rfl

/-- Multi-index-list `get!`, lines 1664-1669. -/
def method1664 (fill : δ → α → Jl δ) (indcopy : σ → ι → κ × κ)
    (size : β → σ) (copy : δ → β → κ → κ → Jl δ)
    (x : δ) (a : β) (indices : ι) (default : α) : Jl δ := do
  let x ← fill x default
  let pair := indcopy (size a) indices
  copy x a pair.1 pair.2
def Property1664 : Prop := ∀ (δ α σ ι κ β : Type) (fill : δ → α → Jl δ)
    (indcopy : σ → ι → κ × κ) (size : β → σ) (copy : δ → β → κ → κ → Jl δ)
    x a indices default,
  method1664 fill indcopy size copy x a indices default = do
    let x ← fill x default
    let pair := indcopy (size a) indices
    copy x a pair.1 pair.2
theorem property1664 : Property1664 := by unfold Property1664; intros; rfl

/-- Multi-index-list defaulted `get`, lines 1671-1672. -/
def method1671 (typeof : α → τ) (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) (a : δ) (indices : ι) (default : α) : γ :=
  getBang (similar a (typeof default) (shape indices)) a indices default
def Property1671 : Prop := ∀ (α τ ι σ δ β γ : Type) (typeof : α → τ)
    (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) a indices default,
  method1671 typeof shape similar getBang a indices default =
    getBang (similar a (typeof default) (shape indices)) a indices default
theorem property1671 : Property1671 := by unfold Property1671; intros; rfl

/-- Matrix printing replacement, line 1675. -/
def method1675 (_a : α) (_i _j : Int) (text : String) : String := text
def Property1675 : Prop := ∀ (α : Type) (a : α) i j text,
  method1675 a i j text = text
theorem property1675 : Property1675 := by unfold Property1675; intros; rfl

/-- Vector printing replacement, line 1676. -/
def method1676 (_a : α) (_i _j : Int) (text : String) : String := text
def Property1676 : Prop := ∀ (α : Type) (a : α) i j text,
  method1676 a i j text = text
theorem property1676 : Property1676 := by unfold Property1676; intros; rfl

/-- Generic `eltypeof`, line 1679. -/
def method1679 (typeof : α → β) (x : α) : β := typeof x
def Property1679 : Prop := ∀ (α β : Type) (typeof : α → β) x,
  method1679 typeof x = typeof x
theorem property1679 : Property1679 := by unfold Property1679; intros; rfl

/-- Array `eltypeof`, line 1680. -/
def method1680 (eltype : α → β) (x : α) : β := eltype x
def Property1680 : Prop := ∀ (α β : Type) (eltype : α → β) x,
  method1680 eltype x = eltype x
theorem property1680 : Property1680 := by unfold Property1680; intros; rfl

/-- Zero-argument `promote_eltypeof`, line 1682. -/
def method1682 : Except String α := .error "promotion requires an argument"
def Property1682 : Prop := ∀ (α : Type), (method1682 : Except String α) = .error "promotion requires an argument"
theorem property1682 : Property1682 := by unfold Property1682; intros; rfl

/-- Unary `promote_eltypeof`, line 1683. -/
def method1683 (eltypeof : α → τ) (v : α) : τ := eltypeof v
def Property1683 : Prop := ∀ (α τ : Type) (eltypeof : α → τ) v,
  method1683 eltypeof v = eltypeof v
theorem property1683 : Property1683 := by unfold Property1683; intros; rfl

/-- Binary `promote_eltypeof`, line 1684. -/
def method1684 (eltypeof : α → τ) (promote : τ → τ → τ) (a b : α) : τ :=
  promote (eltypeof a) (eltypeof b)
def Property1684 : Prop := ∀ (α τ : Type) (eltypeof : α → τ)
    (promote : τ → τ → τ) a b,
  method1684 eltypeof promote a b = promote (eltypeof a) (eltypeof b)
theorem property1684 : Property1684 := by unfold Property1684; intros; rfl

/-- Vararg `promote_eltypeof`, line 1685. -/
def method1685 (eltypeof : α → τ) (promote : τ → τ → τ) (a b : α) (rest : List α) : τ :=
  rest.foldl (fun t x => promote t (eltypeof x)) (promote (eltypeof a) (eltypeof b))
def Property1685 : Prop := ∀ (α τ : Type) (eltypeof : α → τ)
    (promote : τ → τ → τ) a b rest,
  method1685 eltypeof promote a b rest =
    rest.foldl (fun t x => promote t (eltypeof x)) (promote (eltypeof a) (eltypeof b))
theorem property1685 : Property1685 := by unfold Property1685; intros; rfl

/-- Same-type `promote_eltypeof`, line 1686. -/
def method1686 (eltypeof : α → τ) (first : α) (_rest : List α) : τ := eltypeof first
def Property1686 : Prop := ∀ (α τ : Type) (eltypeof : α → τ) first rest,
  method1686 eltypeof first rest = eltypeof first
theorem property1686 : Property1686 := by unfold Property1686; intros; rfl

/-- Same-element-array `promote_eltypeof`, line 1687. -/
def method1687 (elementType : τ) (_arrays : List α) : τ := elementType
def Property1687 : Prop := ∀ (τ α : Type) (elementType : τ) arrays,
  method1687 elementType (arrays : List α) = elementType
theorem property1687 : Property1687 := by unfold Property1687; intros; rfl

/-- Zero-argument `promote_eltype`, line 1689. -/
def method1689 : Except String α := .error "promotion requires an argument"
def Property1689 : Prop := ∀ (α : Type), (method1689 : Except String α) = .error "promotion requires an argument"
theorem property1689 : Property1689 := by unfold Property1689; intros; rfl

/-- Unary `promote_eltype`, line 1690. -/
def method1690 (eltype : α → τ) (v : α) : τ := eltype v
def Property1690 : Prop := ∀ (α τ : Type) (eltype : α → τ) v,
  method1690 eltype v = eltype v
theorem property1690 : Property1690 := by unfold Property1690; intros; rfl

/-- Binary `promote_eltype`, line 1691. -/
def method1691 (eltype : α → τ) (promote : τ → τ → τ) (a b : α) : τ :=
  promote (eltype a) (eltype b)
def Property1691 : Prop := ∀ (α τ : Type) (eltype : α → τ)
    (promote : τ → τ → τ) a b,
  method1691 eltype promote a b = promote (eltype a) (eltype b)
theorem property1691 : Property1691 := by unfold Property1691; intros; rfl

/-- Vararg `promote_eltype`, line 1692. -/
def method1692 (eltype : α → τ) (promote : τ → τ → τ) (a b : α) (rest : List α) : τ :=
  rest.foldl (fun t x => promote t (eltype x)) (promote (eltype a) (eltype b))
def Property1692 : Prop := ∀ (α τ : Type) (eltype : α → τ)
    (promote : τ → τ → τ) a b rest,
  method1692 eltype promote a b rest =
    rest.foldl (fun t x => promote t (eltype x)) (promote (eltype a) (eltype b))
theorem property1692 : Property1692 := by unfold Property1692; intros; rfl

/-- Same-type `promote_eltype`, line 1693. -/
def method1693 (eltypeType : τ → σ) (typeTag : τ) (_values : List α) : σ := eltypeType typeTag
def Property1693 : Prop := ∀ (τ σ α : Type) (eltypeType : τ → σ) typeTag values,
  method1693 eltypeType typeTag (values : List α) = eltypeType typeTag
theorem property1693 : Property1693 := by unfold Property1693; intros; rfl

/-- Same-element-array `promote_eltype`, line 1694. -/
def method1694 (elementType : τ) (_arrays : List α) : τ := elementType
def Property1694 : Prop := ∀ (τ α : Type) (elementType : τ) arrays,
  method1694 elementType (arrays : List α) = elementType
theorem property1694 : Property1694 := by unfold Property1694; intros; rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 1548 "parent" "parent(::AbstractArray)" "An unwrapped AbstractArray is its own parent." "base/abstractarray.jl:1548" ``Property1548 ``property1548,
  entry 1566 "unalias" "unalias(dest,::AbstractArray)" "Array unalias copies exactly when mightalias is true." "base/abstractarray.jl:1566" ``Property1566 ``property1566,
  entry 1567 "unalias" "unalias(dest,::AbstractRange)" "Ranges are returned unchanged." "base/abstractarray.jl:1567" ``Property1567 ``property1567,
  entry 1568 "unalias" "unalias(dest,A)" "The generic fallback returns A unchanged." "base/abstractarray.jl:1568" ``Property1568 ``property1568,
  entry 1582 "unaliascopy" "unaliascopy(::Array)" "Array unaliascopy delegates to copy." "base/abstractarray.jl:1582" ``Property1582 ``property1582,
  entry 1583 "unaliascopy" "unaliascopy(::AbstractArray)" "The method copies first, then checks the copy type through _unaliascopy." "base/abstractarray.jl:1583" ``Property1583 ``property1583,
  entry 1584 "private-unaliascopy" "_unaliascopy(A::T,C::T)" "A same-type preventative copy returns C." "base/abstractarray.jl:1584" ``Property1584 ``property1584,
  entry 1585 "private-unaliascopy" "_unaliascopy(A,C)" "A wrong-type preventative copy throws ArgumentError." "base/abstractarray.jl:1585-1592" ``Property1585 ``property1585,
  entry 1593 "unaliascopy" "unaliascopy(A)" "The generic fallback returns A unchanged." "base/abstractarray.jl:1593" ``Property1593 ``property1593,
  entry 1603 "mightalias" "mightalias(::AbstractArray,::AbstractArray)" "Alias detection short-circuits isbits, emptiness, dataids, and disjointness in source order." "base/abstractarray.jl:1603" ``Property1603 ``property1603,
  entry 1604 "mightalias" "mightalias(x,y)" "The generic alias fallback is false." "base/abstractarray.jl:1604" ``Property1604 ``property1604,
  entry 1606 "isdisjoint" "_isdisjoint((),())" "Two empty identity tuples are disjoint." "base/abstractarray.jl:1606" ``Property1606 ``property1606,
  entry 1607 "isdisjoint" "_isdisjoint((),(b,))" "An empty left tuple is disjoint from a singleton." "base/abstractarray.jl:1607" ``Property1607 ``property1607,
  entry 1608 "isdisjoint" "_isdisjoint((),bs)" "An empty left tuple is disjoint from every tuple." "base/abstractarray.jl:1608" ``Property1608 ``property1608,
  entry 1609 "isdisjoint" "_isdisjoint((a,),())" "A singleton is disjoint from an empty tuple." "base/abstractarray.jl:1609" ``Property1609 ``property1609,
  entry 1610 "isdisjoint" "_isdisjoint((a,),(b,))" "Two singleton identities are disjoint exactly when unequal." "base/abstractarray.jl:1610" ``Property1610 ``property1610,
  entry 1611 "isdisjoint" "_isdisjoint((a,),bs)" "A singleton is disjoint exactly when its identity is absent from bs." "base/abstractarray.jl:1611" ``Property1611 ``property1611,
  entry 1612 "isdisjoint" "_isdisjoint(as,())" "Every tuple is disjoint from an empty tuple." "base/abstractarray.jl:1612" ``Property1612 ``property1612,
  entry 1613 "isdisjoint" "_isdisjoint(as,(b,))" "A tuple is disjoint from a singleton exactly when b is absent." "base/abstractarray.jl:1613" ``Property1613 ``property1613,
  entry 1614 "isdisjoint" "_isdisjoint(as,bs)" "The recursive method checks the head against bs before recurring on the tail." "base/abstractarray.jl:1614" ``Property1614 ``property1614,
  entry 1626 "dataids" "dataids(::AbstractArray)" "The generic array identity tuple contains objectid(A)." "base/abstractarray.jl:1626" ``Property1626 ``property1626,
  entry 1627 "dataids" "dataids(::Memory)" "Memory identity is the unsigned pointer value." "base/abstractarray.jl:1627" ``Property1627 ``property1627,
  entry 1628 "dataids" "dataids(::Array)" "Array dataids delegates through its backing memory." "base/abstractarray.jl:1628" ``Property1628 ``property1628,
  entry 1629 "dataids" "dataids(::AbstractRange)" "Ranges report no mutable data identities." "base/abstractarray.jl:1629" ``Property1629 ``property1629,
  entry 1630 "dataids" "dataids(x)" "The generic fallback reports no data identities." "base/abstractarray.jl:1630" ``Property1630 ``property1630,
  entry 1637 "get" "get(A,i,default)" "Scalar get checks bounds before indexing or returning the value default." "base/abstractarray.jl:1637" ``Property1637 ``property1637,
  entry 1638 "get" "get(A,(),default)" "Zero-index get checks bounds before indexing or returning the value default." "base/abstractarray.jl:1638" ``Property1638 ``property1638,
  entry 1639 "get" "get(A,I::Dims,default)" "Dim-tuple get checks bounds before indexing or returning the value default." "base/abstractarray.jl:1639" ``Property1639 ``property1639,
  entry 1640 "get" "get(f,A,i)" "Callable scalar get invokes the fallback only when out of bounds." "base/abstractarray.jl:1640" ``Property1640 ``property1640,
  entry 1641 "get" "get(f,A,())" "Callable zero-index get invokes the fallback only when out of bounds." "base/abstractarray.jl:1641" ``Property1641 ``property1641,
  entry 1642 "get" "get(f,A,I::Dims)" "Callable dim-tuple get invokes the fallback only when out of bounds." "base/abstractarray.jl:1642" ``Property1642 ``property1642,
  entry 1644 "getbang" "get!(X::AbstractVector,A,I,default)" "The vector method copies valid positions, then fills prefix and suffix ranges using offset axes." "base/abstractarray.jl:1644-1652" ``Property1644 ``property1644,
  entry 1653 "getbang" "get!(X::AbstractArray,A,I,default)" "The linear method copies valid positions, then fills prefix and suffix views." "base/abstractarray.jl:1653-1660" ``Property1653 ``property1653,
  entry 1662 "get" "get(A,range,default)" "The range wrapper computes default type and index shape before allocating and calling get!." "base/abstractarray.jl:1662" ``Property1662 ``property1662,
  entry 1664 "getbang" "get!(X,A,index-list,default)" "The multidimensional method fills defaults, computes source and destination indices, then copies." "base/abstractarray.jl:1664-1669" ``Property1664 ``property1664,
  entry 1671 "get" "get(A,index-list,default)" "The index-list wrapper computes default type and index shape before allocating and calling get!." "base/abstractarray.jl:1671-1672" ``Property1671 ``property1671,
  entry 1675 "replace-print" "replace_in_print_matrix(::AbstractMatrix,...)" "The matrix printing hook returns its supplied string." "base/abstractarray.jl:1675" ``Property1675 ``property1675,
  entry 1676 "replace-print" "replace_in_print_matrix(::AbstractVector,...)" "The vector printing hook returns its supplied string." "base/abstractarray.jl:1676" ``Property1676 ``property1676,
  entry 1679 "eltypeof" "eltypeof(x)" "Generic eltypeof delegates to typeof." "base/abstractarray.jl:1679" ``Property1679 ``property1679,
  entry 1680 "eltypeof" "eltypeof(::AbstractArray)" "Array eltypeof delegates to eltype." "base/abstractarray.jl:1680" ``Property1680 ``property1680,
  entry 1682 "promote-eltypeof" "promote_eltypeof()" "Zero-argument promotion throws." "base/abstractarray.jl:1682" ``Property1682 ``property1682,
  entry 1683 "promote-eltypeof" "promote_eltypeof(v1)" "Unary promotion returns eltypeof(v1)." "base/abstractarray.jl:1683" ``Property1683 ``property1683,
  entry 1684 "promote-eltypeof" "promote_eltypeof(v1,v2)" "Binary promotion computes both element types before promote_type." "base/abstractarray.jl:1684" ``Property1684 ``property1684,
  entry 1685 "promote-eltypeof" "promote_eltypeof(v1,v2,vs...)" "Vararg promotion left-folds promote_type over remaining element types." "base/abstractarray.jl:1685" ``Property1685 ``property1685,
  entry 1686 "promote-eltypeof" "promote_eltypeof(v1::T,vs::T...)" "Same-type values use eltypeof(v1)." "base/abstractarray.jl:1686" ``Property1686 ``property1686,
  entry 1687 "promote-eltypeof" "promote_eltypeof(::AbstractArray{T}...)" "Same-element arrays return T." "base/abstractarray.jl:1687" ``Property1687 ``property1687,
  entry 1689 "promote-eltype" "promote_eltype()" "Zero-argument array promotion throws." "base/abstractarray.jl:1689" ``Property1689 ``property1689,
  entry 1690 "promote-eltype" "promote_eltype(v1)" "Unary array promotion returns eltype(v1)." "base/abstractarray.jl:1690" ``Property1690 ``property1690,
  entry 1691 "promote-eltype" "promote_eltype(v1,v2)" "Binary array promotion computes both eltypes before promote_type." "base/abstractarray.jl:1691" ``Property1691 ``property1691,
  entry 1692 "promote-eltype" "promote_eltype(v1,v2,vs...)" "Vararg array promotion left-folds promote_type over remaining eltypes." "base/abstractarray.jl:1692" ``Property1692 ``property1692,
  entry 1693 "promote-eltype" "promote_eltype(v1::T,vs::T...)" "Same-type values return eltype(T)." "base/abstractarray.jl:1693" ``Property1693 ``property1693,
  entry 1694 "promote-eltype" "promote_eltype(::AbstractArray{T}...)" "Same-element arrays return T." "base/abstractarray.jl:1694" ``Property1694 ``property1694
]

end JuliaLean.AbstractArrayCov.Rows.AliasGet
