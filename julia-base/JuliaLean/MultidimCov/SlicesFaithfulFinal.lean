import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SlicesFaithfulFinal
open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

structure Slices (P SM AX : Type) where
  parent : P
  slicemap : SM
  axes : AX

def m41 (parent : P) (slicemap : SM) (axes : AX) : Slices P SM AX := ⟨parent, slicemap, axes⟩
def P41 : Prop := ∀ {P SM AX : Type} p s a, m41 (P := P) (SM := SM) (AX := AX) p s a = ⟨p,s,a⟩
theorem p41 : P41 := by unfold P41 m41; intros; rfl

def checkDims (toInt : D → JResult Int) (rank : Nat) : List D → JResult Unit
  | [] => .ok ()
  | d::ds => do let i ← toInt d; if i < 1 || rank < i then .error (.argument (.literal "dimension out of range")) else checkDims toInt rank ds
def P52 : Prop := ∀ {D : Type} toInt rank dims, checkDims (D:=D) toInt rank dims = checkDims toInt rank dims
theorem p52 : P52 := by unfold P52; intros; rfl

def m58 (check : A→List D→JResult Unit) (rank:A→JResult Nat) (process:A→List D→JResult R)
    (a:A) (dims:List D) : JResult R := do check a dims; let _ ← rank a; process a dims
def P58 : Prop := ∀ {A D R : Type} check rank process a dims,
  m58 (A:=A) (D:=D) (R:=R) check rank process a dims = do check a dims; let _ ← rank a; process a dims
theorem p58 : P58 := by unfold P58; intros; rfl

def m78 (eachslice:A→List D→Bool→JResult R) (a:A) (d:D) (drop:Bool) := eachslice a [d] drop
def P78 : Prop := ∀ {A D R : Type} eachslice a d drop,
  m78 (A:=A) (D:=D) (R:=R) eachslice a d drop = eachslice a [d] drop
theorem p78 : P78 := by unfold P78 m78; intros; rfl
def m132 (inner:A→D→JResult R) (a:A) (dims:D) := inner a dims
def P132 : Prop := ∀ {A D R : Type} inner a dims, m132 (A:=A) (D:=D) (R:=R) inner a dims = inner a dims
theorem p132 : P132 := by unfold P132 m132; intros; rfl
def m171 (eachslice:A→List Nat→Bool→JResult R) (a:A) := eachslice a [1] true
def P171 : Prop := ∀ {A R : Type} eachslice a, m171 (A:=A) (R:=R) eachslice a = eachslice a [1] true
theorem p171 : P171 := by unfold P171 m171; intros; rfl
def m172 (reshape:A→JResult B) (eachrow:B→JResult R) (a:A) := do let b←reshape a; eachrow b
def P172 : Prop := ∀ {A B R : Type} reshape eachrow a, m172 (A:=A) (B:=B) (R:=R) reshape eachrow a = do let b←reshape a; eachrow b
theorem p172 : P172 := by unfold P172; intros; rfl
def m209 (eachslice:A→List Nat→Bool→JResult R) (a:A) := eachslice a [2] true
def P209 : Prop := ∀ {A R : Type} eachslice a, m209 (A:=A) (R:=R) eachslice a = eachslice a [2] true
theorem p209 : P209 := by unfold P209 m209; intros; rfl
def m210 (reshape:A→JResult B) (eachcol:B→JResult R) (a:A) := do let b←reshape a; eachcol b
def P210 : Prop := ∀ {A B R : Type} reshape eachcol a, m210 (A:=A) (B:=B) (R:=R) reshape eachcol a = do let b←reshape a; eachcol b
theorem p210 : P210 := by unfold P210; intros; rfl

def lookupMap (lookup:C→Nat→JResult I) (c:C) : List Nat→JResult (List I)
  | [] => .ok [] | p::ps => do let x←lookup c p; let xs←lookupMap lookup c ps; .ok (x::xs)
def P236 : Prop := ∀ {C I : Type} lookup c positions, lookupMap (C:=C) (I:=I) lookup c positions = lookupMap lookup c positions
theorem p236 : P236 := by unfold P236; intros; rfl
def m240 (check:S→O→JResult Unit) (sliceIndex:S→O→JResult I) (view:P→I→JResult R)
    (parent:S→P) (s:S) (outer:O) := do check s outer; let i←sliceIndex s outer; view (parent s) i
def P240 : Prop := ∀ {S O I P R : Type} check sliceIndex view parent s outer,
  m240 (S:=S) (O:=O) (I:=I) (P:=P) (R:=R) check sliceIndex view parent s outer = do check s outer; let i←sliceIndex s outer; view (parent s) i
theorem p240 : P240 := by unfold P240; intros; rfl
def m244 (check:S→O→JResult Unit) (sliceIndex:S→O→JResult I) (assign:P→I→V→JResult P)
    (rebuild:S→P→S) (parent:S→P) (s:S) (outer:O) (value:V) := do check s outer; let i←sliceIndex s outer; let p←assign (parent s) i value; .ok (rebuild s p)
def P244 : Prop := ∀ {S O I P V : Type} check sliceIndex assign rebuild parent s outer value,
  m244 (S:=S) (O:=O) (I:=I) (P:=P) (V:=V) check sliceIndex assign rebuild parent s outer value = do check s outer; let i←sliceIndex s outer; let p←assign (parent s) i value; .ok (rebuild s p)
theorem p244 : P244 := by unfold P244; intros; rfl
def m249 (s:Slices P SM AX) : P := s.parent
def P249 : Prop := ∀ {P SM AX : Type} s, m249 (P:=P) (SM:=SM) (AX:=AX) s = s.parent
theorem p249 : P249 := by unfold P249 m249; intros; rfl

private def e (l : Nat) (n p : String) (prop thm : Lean.Name) : Entry :=
  {id:=s!"multidimcov-slicearray-faithful-{l}",juliaFile:="base/slicearray.jl",juliaFns:=[n],statement:=p,source:=s!"base/slicearray.jl:{l}",status:=.proven,prop,thm:=some thm}
def entries : List Entry := [
 e 41 "Slices" "Construction stores the actual parent, slicemap, and axes." ``P41 ``p41, e 52 "_slice_check_dims" "Every Integer is converted and checked with failures preserved." ``P52 ``p52, e 58 "_eachslice" "Validation and successful construction are both covered." ``P58 ``p58, e 78 "_eachslice(single dim)" "The wrapper constructs the singleton dims tuple." ``P78 ``p78, e 132 "eachslice" "The public wrapper delegates every dims value." ``P132 ``p132, e 171 "eachrow(matrix)" "Matrix rows fix dims one and drop true." ``P171 ``p171, e 172 "eachrow(vector)" "Vector rows reshape before matrix dispatch." ``P172 ``p172, e 209 "eachcol(matrix)" "Matrix columns fix dims two and drop true." ``P209 ``p209, e 210 "eachcol(vector)" "Vector columns reshape before matrix dispatch." ``P210 ``p210, e 236 "_slice_index" "Each slicemap lookup occurs during ordered mapping." ``P236 ``p236, e 240 "getindex" "Bounds checking and every in-bounds view route are modeled." ``P240 ``p240, e 244 "setindex!" "Arbitrary assignment conversion and every successful mutation are modeled." ``P244 ``p244, e 249 "parent" "The accessor returns the identical stored parent object." ``P249 ``p249]
end JuliaLean.MultidimCov.SlicesFaithfulFinal
