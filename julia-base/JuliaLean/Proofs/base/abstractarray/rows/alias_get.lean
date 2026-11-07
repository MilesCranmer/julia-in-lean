import JuliaLean.base.abstractarray
import JuliaLean.Proofs.base.abstractarray.rows.index


namespace JuliaLean.AbstractArrayCov.Rows.AliasGet

open JuliaLean
open JuliaLean.Registry

def Property1548 : Prop := ∀ (α : Type) (a : α), method1548 a = a
theorem property1548 : Property1548 := by unfold Property1548; intros; rfl

def Property1566 : Prop := ∀ (δ α : Type) (mightalias : δ → α → Bool)
    (copy : α → α) dest a,
  method1566 mightalias copy dest a = if mightalias dest a then copy a else a
theorem property1566 : Property1566 := by unfold Property1566; intros; rfl

def Property1567 : Prop := ∀ (δ α : Type) (dest : δ) (a : α), method1567 dest a = a
theorem property1567 : Property1567 := by unfold Property1567; intros; rfl

def Property1568 : Prop := ∀ (δ α : Type) (dest : δ) (a : α), method1568 dest a = a
theorem property1568 : Property1568 := by unfold Property1568; intros; rfl

def Property1582 : Prop := ∀ (α β : Type) (copy : α → β) a,
  method1582 copy a = copy a
theorem property1582 : Property1582 := by unfold Property1582; intros; rfl

def Property1583 : Prop := ∀ (α β : Type) (copy : α → β)
    (finish : α → β → Jl α) a,
  method1583 copy finish a = finish a (copy a)
theorem property1583 : Property1583 := by unfold Property1583; intros; rfl

def Property1584 : Prop := ∀ (α : Type) a copy, method1584 (α := α) a copy = copy
theorem property1584 : Property1584 := by unfold Property1584; intros; rfl

def Property1585 : Prop := ∀ (α : Type) arrayType copyType,
  (method1585 arrayType copyType : Jl α) =
    .error (.argumentError ("copy(::" ++ arrayType ++ ") returns " ++ copyType))
theorem property1585 : Property1585 := by unfold Property1585; intros; rfl

def Property1593 : Prop := ∀ (α : Type) (a : α), method1593 a = a
theorem property1593 : Property1593 := by unfold Property1593; intros; rfl

def Property1603 : Prop := ∀ (α : Type) (isbits isempty : α → Bool)
    (dataids : α → List Nat) disjoint a b,
  method1603 isbits isempty dataids disjoint a b =
    (!isbits a && !isbits b && !isempty a && !isempty b && !disjoint (dataids a) (dataids b))
theorem property1603 : Property1603 := by unfold Property1603; intros; rfl

def Property1604 : Prop := ∀ (_x _y : Nat), method1604 = false
theorem property1604 : Property1604 := by unfold Property1604; intros; rfl

def Property1606 : Prop := ∀ _empty : Unit, method1606 = true
theorem property1606 : Property1606 := by unfold Property1606; intros; rfl

def Property1607 : Prop := ∀ b, method1607 b = true
theorem property1607 : Property1607 := by unfold Property1607; intros; rfl

def Property1608 : Prop := ∀ bs, method1608 bs = true
theorem property1608 : Property1608 := by unfold Property1608; intros; rfl

def Property1609 : Prop := ∀ a, method1609 a = true
theorem property1609 : Property1609 := by unfold Property1609; intros; rfl

def Property1610 : Prop := ∀ a b, method1610 a b = (a != b)
theorem property1610 : Property1610 := by unfold Property1610; intros; rfl

def Property1611 : Prop := ∀ a bs, method1611 a bs = !bs.contains a
theorem property1611 : Property1611 := by unfold Property1611; intros; rfl

def Property1612 : Prop := ∀ as, method1612 as = true
theorem property1612 : Property1612 := by unfold Property1612; intros; rfl

def Property1613 : Prop := ∀ as b, method1613 as b = !as.contains b
theorem property1613 : Property1613 := by unfold Property1613; intros; rfl

def Property1614 : Prop := ∀ recurse as bs,
  method1614 recurse as bs = match as with
    | [] => true
    | a :: rest => !bs.contains a && recurse rest bs
theorem property1614 : Property1614 := by
  unfold Property1614
  intro recurse as bs
  cases as <;> rfl

def Property1626 : Prop := ∀ (α : Type) (objectid : α → Nat) a,
  method1626 objectid a = [objectid a]
theorem property1626 : Property1626 := by unfold Property1626; intros; rfl

def Property1627 : Prop := ∀ (α : Type) (pointer : α → Nat) a,
  method1627 pointer a = [pointer a]
theorem property1627 : Property1627 := by unfold Property1627; intros; rfl

def Property1628 : Prop := ∀ (α β : Type) (memory : α → β)
    (dataids : β → List Nat) a,
  method1628 memory dataids a = dataids (memory a)
theorem property1628 : Property1628 := by unfold Property1628; intros; rfl

def Property1629 : Prop := ∀ _range : Unit, method1629 = []
theorem property1629 : Property1629 := by unfold Property1629; intros; rfl

def Property1630 : Prop := ∀ _value : Nat, method1630 = []
theorem property1630 : Property1630 := by unfold Property1630; intros; rfl

def Property1637 : Prop := ∀ (α β : Type) (check : α → Int → Bool)
    (get : α → Int → β) a i default,
  method1637 check get a i default = if check a i then get a i else default
theorem property1637 : Property1637 := by unfold Property1637; intros; rfl

def Property1638 : Prop := ∀ (α β : Type) (check : α → Bool) (get : α → β) a default,
  method1638 check get a default = if check a then get a else default
theorem property1638 : Property1638 := by unfold Property1638; intros; rfl

def Property1639 : Prop := ∀ (α β : Type) (check : α → List Int → Bool)
    (get : α → List Int → β) a indices default,
  method1639 check get a indices default = if check a indices then get a indices else default
theorem property1639 : Property1639 := by unfold Property1639; intros; rfl

def Property1640 : Prop := ∀ (α β : Type) (check : α → Int → Bool)
    (get : α → Int → β) fallback a i,
  method1640 check get fallback a i = if check a i then get a i else fallback ()
theorem property1640 : Property1640 := by unfold Property1640; intros; rfl

def Property1641 : Prop := ∀ (α β : Type) (check : α → Bool)
    (get : α → β) fallback a,
  method1641 check get fallback a = if check a then get a else fallback ()
theorem property1641 : Property1641 := by unfold Property1641; intros; rfl

def Property1642 : Prop := ∀ (α β : Type) (check : α → List Int → Bool)
    (get : α → List Int → β) fallback a indices,
  method1642 check get fallback a indices =
    if check a indices then get a indices else fallback ()
theorem property1642 : Property1642 := by unfold Property1642; intros; rfl

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

def Property1662 : Prop := ∀ (α τ ι σ δ β γ : Type) (typeof : α → τ)
    (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) a indices default,
  method1662 typeof shape similar getBang a indices default =
    getBang (similar a (typeof default) (shape indices)) a indices default
theorem property1662 : Property1662 := by unfold Property1662; intros; rfl

def Property1664 : Prop := ∀ (δ α σ ι κ β : Type) (fill : δ → α → Jl δ)
    (indcopy : σ → ι → κ × κ) (size : β → σ) (copy : δ → β → κ → κ → Jl δ)
    x a indices default,
  method1664 fill indcopy size copy x a indices default = do
    let x ← fill x default
    let pair := indcopy (size a) indices
    copy x a pair.1 pair.2
theorem property1664 : Property1664 := by unfold Property1664; intros; rfl

def Property1671 : Prop := ∀ (α τ ι σ δ β γ : Type) (typeof : α → τ)
    (shape : ι → σ) (similar : δ → τ → σ → β)
    (getBang : β → δ → ι → α → γ) a indices default,
  method1671 typeof shape similar getBang a indices default =
    getBang (similar a (typeof default) (shape indices)) a indices default
theorem property1671 : Property1671 := by unfold Property1671; intros; rfl

def Property1675 : Prop := ∀ (α : Type) (a : α) i j text,
  method1675 a i j text = text
theorem property1675 : Property1675 := by unfold Property1675; intros; rfl

def Property1676 : Prop := ∀ (α : Type) (a : α) i j text,
  method1676 a i j text = text
theorem property1676 : Property1676 := by unfold Property1676; intros; rfl

def Property1679 : Prop := ∀ (α β : Type) (typeof : α → β) x,
  method1679 typeof x = typeof x
theorem property1679 : Property1679 := by unfold Property1679; intros; rfl

def Property1680 : Prop := ∀ (α β : Type) (eltype : α → β) x,
  method1680 eltype x = eltype x
theorem property1680 : Property1680 := by unfold Property1680; intros; rfl

def Property1682 : Prop := ∀ (α : Type), (method1682 : Except String α) = .error "promotion requires an argument"
theorem property1682 : Property1682 := by unfold Property1682; intros; rfl

def Property1683 : Prop := ∀ (α τ : Type) (eltypeof : α → τ) v,
  method1683 eltypeof v = eltypeof v
theorem property1683 : Property1683 := by unfold Property1683; intros; rfl

def Property1684 : Prop := ∀ (α τ : Type) (eltypeof : α → τ)
    (promote : τ → τ → τ) a b,
  method1684 eltypeof promote a b = promote (eltypeof a) (eltypeof b)
theorem property1684 : Property1684 := by unfold Property1684; intros; rfl

def Property1685 : Prop := ∀ (α τ : Type) (eltypeof : α → τ)
    (promote : τ → τ → τ) a b rest,
  method1685 eltypeof promote a b rest =
    rest.foldl (fun t x => promote t (eltypeof x)) (promote (eltypeof a) (eltypeof b))
theorem property1685 : Property1685 := by unfold Property1685; intros; rfl

def Property1686 : Prop := ∀ (α τ : Type) (eltypeof : α → τ) first rest,
  method1686 eltypeof first rest = eltypeof first
theorem property1686 : Property1686 := by unfold Property1686; intros; rfl

def Property1687 : Prop := ∀ (τ α : Type) (elementType : τ) arrays,
  method1687 elementType (arrays : List α) = elementType
theorem property1687 : Property1687 := by unfold Property1687; intros; rfl

def Property1689 : Prop := ∀ (α : Type), (method1689 : Except String α) = .error "promotion requires an argument"
theorem property1689 : Property1689 := by unfold Property1689; intros; rfl

def Property1690 : Prop := ∀ (α τ : Type) (eltype : α → τ) v,
  method1690 eltype v = eltype v
theorem property1690 : Property1690 := by unfold Property1690; intros; rfl

def Property1691 : Prop := ∀ (α τ : Type) (eltype : α → τ)
    (promote : τ → τ → τ) a b,
  method1691 eltype promote a b = promote (eltype a) (eltype b)
theorem property1691 : Property1691 := by unfold Property1691; intros; rfl

def Property1692 : Prop := ∀ (α τ : Type) (eltype : α → τ)
    (promote : τ → τ → τ) a b rest,
  method1692 eltype promote a b rest =
    rest.foldl (fun t x => promote t (eltype x)) (promote (eltype a) (eltype b))
theorem property1692 : Property1692 := by unfold Property1692; intros; rfl

def Property1693 : Prop := ∀ (τ σ α : Type) (eltypeType : τ → σ) typeTag values,
  method1693 eltypeType typeTag (values : List α) = eltypeType typeTag
theorem property1693 : Property1693 := by unfold Property1693; intros; rfl

def Property1694 : Prop := ∀ (τ α : Type) (elementType : τ) arrays,
  method1694 elementType (arrays : List α) = elementType
theorem property1694 : Property1694 := by unfold Property1694; intros; rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.AliasGet
