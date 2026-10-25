import JuliaLean.Strings.Ops
import JuliaLean.Strings.Theory
import JuliaLean.Strings.Props
import JuliaLean.Registry.Types

/-!
# AnnotatedString regions

Model of the region bookkeeping of `AnnotatedString` in
`base/strings/annotated.jl` (master `bbfa0ce4150`).

* An `AnnotatedString{String}` is its `String` (`JStr`) and its vector of
  `RegionAnnotation`s (`base/strings/annotated.jl:64-67`). A region annotation
  is a region `lo:hi` (a `UnitRange{Int}`) and a label; the annotation value
  plays no role in any modelled function, so only a `Nat` label is kept, which
  makes the order of annotations observable.
* A `SubString{<:AnnotatedString}` is its parent, `offset` and `ncodeunits`
  (`base/strings/substring.jl:71-106`).
* Region bounds are `Int` (`JInt64`) and use the wrapping `JInt` operators.
  Constructing `a:b` stores `unitrange_last(a, b)` as the end
  (`base/range.jl:428,439-441`): `b` when `b ≥ a`, otherwise `a - 1`.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings JuliaLean.Registry

/-- A `UnitRange{Int}` as its stored `(first, last)`. -/
abbrev Region := JInt64 × JInt64

/-- `RegionAnnotation = @NamedTuple{region::UnitRange{Int}, label::Symbol, value}`,
`base/strings/annotated.jl:3-6`, with a `Nat` label and no value. -/
structure RAnn where
  lo : JInt64
  hi : JInt64
  label : Nat
  deriving DecidableEq

/-- `AnnotatedString{String}`, `base/strings/annotated.jl:64-67`. -/
structure AStr where
  str : JStr
  anns : List RAnn

/-- `SubString{AnnotatedString{String}}`: parent, `offset`, `ncodeunits`
(`base/strings/substring.jl:71-106`). -/
structure ASub where
  parent : AStr
  offset : JInt64
  ncu : JInt64

/-- `a:b` for `a b :: Int`: `UnitRange(a, b)` stores `unitrange_last(a, b)`,
`base/range.jl:428,439-441`, which is `b` when `b ≥ a` and the wrapping
`a - 1` otherwise. -/
def urange (a b : JInt64) : Region := (a, if b.val ≥ a.val then b else a - ix 1)

/-- `isempty(r::AbstractUnitRange) = first(r) > last(r)`, `base/range.jl`. -/
def isemptyR (r : Region) : Bool := decide (r.1.val > r.2.val)

/-- `@inline(setindex(annot, region, :region))`: the annotation with a new region. -/
def RAnn.setR (a : RAnn) (r : Region) : RAnn := { a with lo := r.1, hi := r.2 }

/-! ## `annotations` -/

/-- The loop of `annotations(s::AnnotatedString, pos::UnitRange{<:Integer})`,
`base/strings/annotated.jl:432-443`: keep each annotation whose region meets
`pos` (`intersect(pos, region) = max(first(pos), first(region)):min(last(pos),
last(region))`, `base/range.jl:1199`) and clamp its region to that same range. -/
def annsRange (pos : Region) : List RAnn → List RAnn
  | [] => []
  | ann :: rest =>
    if !isemptyR (urange (imax pos.1 ann.lo) (imin pos.2 ann.hi)) then
      ann.setR (urange (imax pos.1 ann.lo) (imin pos.2 ann.hi)) :: annsRange pos rest
    else annsRange pos rest

/-- `annotations(s::AnnotatedString, pos::UnitRange)`, `base/strings/annotated.jl:432-443`. -/
def annotationsRange (s : AStr) (pos : Region) : List RAnn := annsRange pos s.anns

/-- `annotations(s::AnnotatedString, pos::Integer) = annotations(s, pos:pos)`,
`base/strings/annotated.jl:445`. -/
def annotationsAt (s : AStr) (p : JInt64) : List RAnn := annotationsRange s (urange p p)

/-- The labels of the annotations that apply to position `p`, in order. -/
def labelsAt (s : AStr) (p : JInt64) : List Nat := (annotationsAt s p).map RAnn.label

/-- `annotations(s::SubString{<:AnnotatedString})`, `base/strings/annotated.jl:420-430`:
the parent's annotations over `s.offset+1:s.offset+s.ncodeunits`, shifted by
`-s.offset`. -/
def annotationsSub (s : ASub) : List RAnn :=
  let substrRange := urange (s.offset + ix 1) (s.offset + s.ncu)
  (annotationsRange s.parent substrRange).map fun ann =>
    ann.setR (urange (ann.lo - s.offset) (ann.hi - s.offset))

/-- `annotations(s::SubString{<:AnnotatedString}, pos::Integer) =
annotations(s.string, s.offset + pos)`, `base/strings/annotated.jl:447-448`. -/
def annotationsSubAt (s : ASub) (p : JInt64) : List RAnn := annotationsAt s.parent (s.offset + p)

/-- `annotations(s::SubString{<:AnnotatedString}, pos::UnitRange) =
annotations(s.string, first(pos)+s.offset:last(pos)+s.offset)`,
`base/strings/annotated.jl:450-451`. -/
def annotationsSubRange (s : ASub) (pos : Region) : List RAnn :=
  annotationsRange s.parent (urange (pos.1 + s.offset) (pos.2 + s.offset))

/-! ## `annotatedstring` -/

/-- An argument of `annotatedstring(xs...)`: an `AnnotatedString` or a
`SubString{<:AnnotatedString}`. -/
inductive AArg where
  | str (a : AStr)
  | sub (s : ASub)

/-- `@inline(setindex(annot, annot.region .+ size, :region))`,
`base/strings/annotated.jl:282`; `r .+ x = range(first(r) + x, last(r) + x)` for
a `UnitRange` and an `Integer` (`base/broadcast.jl:1188`). -/
def shiftAnn (size : JInt64) (a : RAnn) : RAnn := a.setR (urange (a.lo + size) (a.hi + size))

/-- `rstart = size + max(0, start - x.offset - 1) + 1`, `base/strings/annotated.jl:289`. -/
def rstartOf (size off : JInt64) (a : RAnn) : JInt64 := size + imax (ix 0) (a.lo - off - ix 1) + ix 1

/-- `rstop = size + min(stop, x.offset + x.ncodeunits) - x.offset`,
`base/strings/annotated.jl:290`. -/
def rstopOf (size off n : JInt64) (a : RAnn) : JInt64 := size + imin a.hi (off + n) - off

/-- The SubString branch of `annotatedstring`, `base/strings/annotated.jl:286-293`. -/
def subAnns (size off n : JInt64) : List RAnn → List RAnn
  | [] => []
  | ann :: rest =>
    if ann.lo.val ≤ (off + n).val ∧ ann.hi.val > off.val then
      ann.setR (urange (rstartOf size off ann) (rstopOf size off n ann)) :: subAnns size off n rest
    else subAnns size off n rest

/-- `print(s, unannotate(x))` for a SubString: `unannotate` is
`raw_substring(parent(s).string, s.offset + 1, ncodeunits(s))` under `@inbounds`
(`base/strings/annotated.jl:186-189`), whose bytes are the parent's code units
`offset+1 .. offset+ncodeunits`. -/
def subBytes (s : ASub) : List UInt8 := (JSub.view ⟨s.parent.str, s.offset, s.ncu⟩).bytes

/-- The loop of `annotatedstring(xs...)`, `base/strings/annotated.jl:278-303`:
`buf` holds the bytes written so far, so `size = filesize(s.io)` is its length. -/
def asLoop : List AArg → List UInt8 → List RAnn → List UInt8 × List RAnn
  | [], buf, anns => (buf, anns)
  | x :: xs, buf, anns =>
    let size := ix buf.length
    match x with
    | .str a => asLoop xs (buf ++ a.str.bytes) (anns ++ a.anns.map (shiftAnn size))
    | .sub s => asLoop xs (buf ++ subBytes s) (anns ++ subAnns size s.offset s.ncu s.parent.anns)

/-- `annotatedstring(xs...)`, `base/strings/annotated.jl:272-306`, for arguments
that are `AnnotatedString`s or SubStrings of them. The `sizehint` (`:274-275`)
only preallocates. A result of `2^62` bytes or more cannot be allocated. -/
def annotatedstring (xs : List AArg) : SJl AStr :=
  match xs with
  | [] => .ok ⟨JStr.empty, []⟩
  | _ :: _ =>
    let r := asLoop xs [] []
    if h : r.1.length < 2 ^ 62 then .ok ⟨⟨r.1, h⟩, r.2⟩ else .error .outOfMemory

/-- `AnnotatedString(s::SubString{<:AnnotatedString}) = annotatedstring(s)`,
`base/strings/annotated.jl:312`. -/
def annotatedStringOfSub (s : ASub) : SJl AStr := annotatedstring [.sub s]

/-! ## `reverse` -/

/-- `reverse(s::AnnotatedString)`, `base/strings/annotated.jl:346-355`. -/
def areverse (s : AStr) : AStr :=
  let lastind := lastindex s.str
  ⟨Strings.reverse s.str, s.anns.map fun annot =>
    annot.setR (urange (ix 1 + lastind - annot.hi) (ix 1 + lastind - annot.lo))⟩

/-! ## `eachregion` -/

/-- An annotation change event `(pos, active, index)`, `base/strings/annotated.jl:596`. -/
structure Event where
  pos : JInt64
  active : Bool
  index : Nat

/-- The loop of `annotation_events`, `base/strings/annotated.jl:597-604`; `i` is
the one-based index from `enumerate`. -/
def eventsLoop (s : JStr) (sub : Region) : Nat → List RAnn → SJl (List Event)
  | _, [] => .ok []
  | i, ann :: rest =>
    if !isemptyR (urange (imax sub.1 ann.lo) (imin sub.2 ann.hi)) then
      let start := imax sub.1 ann.lo
      let stop := imin sub.2 ann.hi
      if !decide (start.val ≤ stop.val) then eventsLoop s sub (i + 1) rest
      else do
        let a ← thisind s start
        let b ← nextind s stop
        let tl ← eventsLoop s sub (i + 1) rest
        pure ({ pos := a, active := true, index := i } :: { pos := b, active := false, index := i } :: tl)
    else eventsLoop s sub (i + 1) rest

/-- Insert `e` before the first event whose position is not smaller. -/
def insertByPos (e : Event) : List Event → List Event
  | [] => [e]
  | f :: fs => if f.pos.val < e.pos.val then f :: insertByPos e fs else e :: f :: fs

/-- `sort(events, by=e -> e.pos)`, `base/strings/annotated.jl:605`. Julia's default
sort is stable, and so is this insertion sort, so both give the same order. -/
def sortByPos : List Event → List Event
  | [] => []
  | e :: es => insertByPos e (sortByPos es)

/-- `annotation_events(s, annots, subregion)`, `base/strings/annotated.jl:595-606`,
called as `annotation_events(s.string, annotations(s), subregion)` (`:608-609`). -/
def annotationEvents (s : JStr) (anns : List RAnn) (sub : Region) : SJl (List Event) := do
  let evs ← eventsLoop s sub 1 anns
  pure (sortByPos evs)

/-- `searchsortedfirst(activelist, idx)` on the sorted `activelist`: one plus the
number of entries smaller than `idx`. -/
def searchsortedfirst (l : List Nat) (x : Nat) : Nat := (l.takeWhile (· < x)).length + 1

/-- `annotvals[activelist]`: indexing throws `BoundsError` outside `1:length`. -/
def pick (annotvals : List Nat) (active : List Nat) : SJl (List Nat) :=
  active.mapM fun k =>
    if 1 ≤ k ∧ k ≤ annotvals.length then .ok (annotvals.getD (k - 1) 0) else .error boundsErr

/-- The `for event in events` loop of `eachregion`, `base/strings/annotated.jl:556-567`.
The state is `pos` and `activelist`. -/
def regionLoop (s : JStr) (annotvals : List Nat) :
    List Event → JInt64 → List Nat → SJl (List (Region × List Nat))
  | [], _, _ => .ok []
  | e :: es, pos, active => do
    let out : List (Region × List Nat) ← if e.pos.val ≠ pos.val then do
        let b ← prevind s e.pos
        let vals ← pick annotvals active
        pure [(urange pos b, vals)]
      else pure []
    let pos := if e.pos.val ≠ pos.val then e.pos else pos
    let k := searchsortedfirst active e.index
    let active : List Nat ← if e.active then pure (active.take (k - 1) ++ e.index :: active.drop (k - 1))
      else if k ≤ active.length then pure (active.eraseIdx (k - 1)) else .error boundsErr
    let rest ← regionLoop s annotvals es pos active
    pure (out ++ rest)

/-- `firstindex(s):lastindex(s)`, the default `subregion` of `eachregion`
(`base/strings/annotated.jl:541`). -/
def defaultRegion (s : AStr) : Region := urange (firstindex s.str) (lastindex s.str)

/-- `eachregion(s::AnnotatedString, subregion)`, `base/strings/annotated.jl:541-573`:
the regions and the labels of `annotvals[activelist]` of the `RegionIterator`.
The guard `isempty(s) || isempty(subregion) && return ...` (`:542-543`) parses as
`isempty(s) || (isempty(subregion) && return ...)`. -/
def eachregion (s : AStr) (sub : Region) : SJl (List (Region × List Nat)) := do
  if !decide ((ncodeunits s.str).val = 0) && isemptyR sub then return []
  let events ← annotationEvents s.str s.anns sub
  match events with
  | [] => return [(sub, [])]
  | e0 :: _ =>
    let annotvals := s.anns.map RAnn.label
    let pos := e0.pos
    let pre : List (Region × List Nat) ← if pos.val > sub.1.val then do
        let a ← thisind s.str sub.1
        let b ← prevind s.str pos
        pure [(urange a b, [])]
      else pure []
    let mid ← regionLoop s.str annotvals events pos []
    let lastPos := (events.getLast?.map Event.pos).getD pos
    let nx ← nextind s.str sub.2
    let post : List (Region × List Nat) ← if lastPos.val < nx.val then do
        let t ← thisind s.str sub.2
        pure [(urange lastPos t, [])]
      else pure []
    return pre ++ mid ++ post

/-- `eachregion(s::SubString{<:AnnotatedString}, pos)`, `base/strings/annotated.jl:575-581`;
`isempty(s)` is `iszero(ncodeunits(s))` (`base/strings/basic.jl:181`). -/
def eachregionSub (s : ASub) (pos : Region) : SJl (List (Region × List Nat)) :=
  if s.ncu.val = 0 then .ok []
  else eachregion s.parent (urange (pos.1 + s.offset) (pos.2 + s.offset))

/-! ## Arithmetic lemmas -/

theorem jb (x : JInt64) : -(2 ^ 63) ≤ x.val ∧ x.val < 2 ^ 63 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem addv {a b : JInt64} {x y : Int} (ha : a.val = x) (hb : b.val = y)
    (h1 : -(2 ^ 63) ≤ x + y) (h2 : x + y < 2 ^ 63) : (a + b).val = x + y := by
  rw [add_val a b (by rw [ha, hb]; exact h1) (by rw [ha, hb]; exact h2), ha, hb]

theorem subv {a b : JInt64} {x y : Int} (ha : a.val = x) (hb : b.val = y)
    (h1 : -(2 ^ 63) ≤ x - y) (h2 : x - y < 2 ^ 63) : (a - b).val = x - y := by
  rw [sub_val a b (by rw [ha, hb]; exact h1) (by rw [ha, hb]; exact h2), ha, hb]

theorem imax_val (x y : JInt64) : (imax x y).val = max x.val y.val := by
  unfold imax; split <;> omega

theorem imin_val (x y : JInt64) : (imin x y).val = min x.val y.val := by
  unfold imin; split <;> omega

theorem imaxv {a b : JInt64} {x y : Int} (ha : a.val = x) (hb : b.val = y) :
    (imax a b).val = max x y := by rw [imax_val, ha, hb]

theorem iminv {a b : JInt64} {x y : Int} (ha : a.val = x) (hb : b.val = y) :
    (imin a b).val = min x y := by rw [imin_val, ha, hb]

theorem decide_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.1 hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.2 hq))]

theorem isemptyR_urange (a b : JInt64) : isemptyR (urange a b) = decide (b.val < a.val) := by
  unfold isemptyR urange
  dsimp only
  split
  · rfl
  · rename_i h
    have hb := jb b
    have e : (a - ix 1).val = a.val - 1 := subv rfl ix1 (by omega) (by have := jb a; omega)
    rw [e]
    exact decide_iff (by constructor <;> intro _ <;> omega)

theorem setR_urange (a : RAnn) (u v : JInt64) :
    (a.setR (urange u v)).lo = u ∧
      (((a.setR (urange u v)).hi.val = v.val ∧ u.val ≤ v.val) ∨
        ((a.setR (urange u v)).hi.val = u.val - 1 ∧ v.val < u.val)) := by
  unfold RAnn.setR urange
  dsimp only
  refine ⟨rfl, ?_⟩
  split
  · rename_i h; left; exact ⟨rfl, h⟩
  · rename_i h
    have hv := jb v
    right
    exact ⟨subv rfl ix1 (by omega) (by have := jb u; omega), by omega⟩

/-- Annotation `a` applies to position `p`: `p ∈ a.region`. -/
def applies (p : JInt64) (a : RAnn) : Bool := decide (a.lo.val ≤ p.val ∧ p.val ≤ a.hi.val)

theorem applies_urange (a : RAnn) (u v p : JInt64) :
    applies p (a.setR (urange u v)) = decide (u.val ≤ p.val ∧ p.val ≤ v.val) := by
  obtain ⟨hlo, hhi⟩ := setR_urange a u v
  unfold applies
  rw [hlo]
  rcases hhi with ⟨hhi, _⟩ | ⟨hhi, _⟩ <;> rw [hhi] <;>
    exact decide_iff (by constructor <;> intro _ <;> omega)

theorem urange_pp (p : JInt64) : urange p p = (p, p) := by
  unfold urange; simp

theorem annsRange_pt_labels (p : JInt64) : ∀ l : List RAnn,
    (annsRange (p, p) l).map RAnn.label = (l.filter (applies p)).map RAnn.label
  | [] => rfl
  | a :: t => by
    have ih := annsRange_pt_labels p t
    have key : (!isemptyR (urange (imax p a.lo) (imin p a.hi))) = applies p a := by
      rw [isemptyR_urange, imax_val, imin_val]
      unfold applies
      by_cases h : a.lo.val ≤ p.val ∧ p.val ≤ a.hi.val
      · rw [decide_eq_false (by omega : ¬ (min p.val a.hi.val < max p.val a.lo.val)), decide_eq_true h]
        rfl
      · rw [decide_eq_true (by omega : min p.val a.hi.val < max p.val a.lo.val), decide_eq_false h]
        rfl
    simp only [annsRange, List.filter_cons, key]
    by_cases hq : applies p a = true <;> simp [hq, ih, RAnn.setR]

/-- `annotations(s, p)` lists, in order, the annotations whose region contains `p`. -/
theorem labelsAt_eq (s : AStr) (p : JInt64) :
    labelsAt s p = (s.anns.filter (applies p)).map RAnn.label := by
  unfold labelsAt annotationsAt annotationsRange
  rw [urange_pp]
  exact annsRange_pt_labels p s.anns

theorem labels_map_filter (l : List RAnn) (f : RAnn → RAnn) (P Q : RAnn → Bool)
    (hlab : ∀ a, (f a).label = a.label) (h : ∀ a ∈ l, P (f a) = Q a) :
    ((l.map f).filter P).map RAnn.label = (l.filter Q).map RAnn.label := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.filter_cons, h a (by simp)]
    by_cases hq : Q a = true <;> simp [hq, hlab, ih']

/-- A region `lo:hi` inside `1:L`, the code units of a string of `L` code units. -/
def InsideN (L : Int) (a : RAnn) : Prop :=
  1 ≤ a.lo.val ∧ a.lo.val ≤ L + 1 ∧ 0 ≤ a.hi.val ∧ a.hi.val ≤ L

/-- Every region of `x` lies inside `1:ncodeunits(x)`. -/
def RegionsInside (x : AStr) : Prop := ∀ a ∈ x.anns, InsideN x.str.bytes.length a

/-! ## Proven properties -/

/-- `annotatedstring(x, y)` writes the bytes of `x` then `y`, and at every code
unit position the annotations of `x` (first part) or of `y` (second part) apply,
in order. Regions of `x` and `y` lie inside their strings. -/
def ConcatLabels : Prop :=
  ∀ x y : AStr, RegionsInside x → RegionsInside y →
    x.str.bytes.length + y.str.bytes.length < 2 ^ 62 →
    ∃ z, annotatedstring [.str x, .str y] = .ok z ∧ z.str.bytes = x.str.bytes ++ y.str.bytes ∧
      ∀ p : JInt64, 1 ≤ p.val → p.val ≤ z.str.bytes.length →
        labelsAt z p = if p.val ≤ x.str.bytes.length then labelsAt x p
          else labelsAt y (p - ncodeunits x.str)

theorem concatLabels_proven : ConcatLabels := by
  intro x y hx hy hlen
  have hL := x.str.small
  have hM := y.str.small
  have hr : asLoop [.str x, .str y] [] [] =
      (x.str.bytes ++ y.str.bytes,
        x.anns.map (shiftAnn (ix 0)) ++ y.anns.map (shiftAnn (ncodeunits x.str))) := by
    simp [asLoop, ncodeunits]
  have hlen' : (x.str.bytes ++ y.str.bytes).length < 2 ^ 62 := by
    simp only [List.length_append]; exact hlen
  have hz : annotatedstring [.str x, .str y] =
      .ok ⟨⟨x.str.bytes ++ y.str.bytes, hlen'⟩,
        x.anns.map (shiftAnn (ix 0)) ++ y.anns.map (shiftAnn (ncodeunits x.str))⟩ := by
    simp only [annotatedstring, hr]
    rw [dif_pos hlen']
  refine ⟨_, hz, rfl, ?_⟩
  intro p hp1 hp2
  simp only [List.length_append] at hp2
  have hnx : (ncodeunits x.str).val = x.str.bytes.length := ncu_val x.str
  rw [labelsAt_eq, labelsAt_eq, labelsAt_eq]
  simp only [List.filter_append, List.map_append]
  split
  · rename_i hpx
    have hA := labels_map_filter x.anns (shiftAnn (ix 0)) (applies p) (applies p) (fun _ => rfl)
      (fun a _ => by
        have e1 : (a.lo + ix 0).val = a.lo.val + 0 := addv rfl ix0 (by have := jb a.lo; omega) (by have := jb a.lo; omega)
        have e2 : (a.hi + ix 0).val = a.hi.val + 0 := addv rfl ix0 (by have := jb a.hi; omega) (by have := jb a.hi; omega)
        rw [shiftAnn, applies_urange, e1, e2]
        unfold applies
        exact decide_iff (by constructor <;> intro _ <;> omega))
    have hB := labels_map_filter y.anns (shiftAnn (ncodeunits x.str)) (applies p) (fun _ => false)
      (fun _ => rfl)
      (fun a ha => by
        have hi := hy a ha
        unfold InsideN at hi
        have e1 : (a.lo + ncodeunits x.str).val = a.lo.val + x.str.bytes.length :=
          addv rfl hnx (by omega) (by omega)
        rw [shiftAnn, applies_urange, e1]
        exact decide_eq_false (by omega))
    rw [hA, hB]
    simp
  · rename_i hpx
    have hp : (p - ncodeunits x.str).val = p.val - x.str.bytes.length :=
      subv rfl hnx (by omega) (by omega)
    have hA := labels_map_filter x.anns (shiftAnn (ix 0)) (applies p) (fun _ => false) (fun _ => rfl)
      (fun a ha => by
        have hi := hx a ha
        unfold InsideN at hi
        have e2 : (a.hi + ix 0).val = a.hi.val + 0 := addv rfl ix0 (by omega) (by omega)
        rw [shiftAnn, applies_urange, e2]
        exact decide_eq_false (by omega))
    have hB := labels_map_filter y.anns (shiftAnn (ncodeunits x.str)) (applies p)
      (applies (p - ncodeunits x.str)) (fun _ => rfl)
      (fun a ha => by
        have hi := hy a ha
        unfold InsideN at hi
        have e1 : (a.lo + ncodeunits x.str).val = a.lo.val + x.str.bytes.length :=
          addv rfl hnx (by omega) (by omega)
        have e2 : (a.hi + ncodeunits x.str).val = a.hi.val + x.str.bytes.length :=
          addv rfl hnx (by omega) (by omega)
        rw [shiftAnn, applies_urange, e1, e2]
        unfold applies
        rw [hp]
        exact decide_iff (by constructor <;> intro _ <;> omega))
    rw [hA, hB]
    simp

theorem rstart_val (L : Int) (hL : L < 2 ^ 62) (off : JInt64) (a : RAnn) (h0 : 0 ≤ off.val)
    (hoL : off.val ≤ L) (h1 : 1 ≤ a.lo.val) (h2 : a.lo.val ≤ L + 1) :
    (rstartOf (ix 0) off a).val = max 0 (a.lo.val - off.val - 1) + 1 := by
  unfold rstartOf
  have e : (ix 0 + imax (ix 0) (a.lo - off - ix 1) + ix 1).val =
      0 + max 0 (a.lo.val - off.val - 1) + 1 :=
    addv (addv ix0 (imaxv ix0 (subv (subv rfl rfl (by omega) (by omega)) ix1 (by omega) (by omega)))
      (by omega) (by omega)) ix1 (by omega) (by omega)
  rw [e]; omega

theorem rstop_val (L : Int) (hL : L < 2 ^ 62) (off n : JInt64) (a : RAnn) (h0 : 0 ≤ off.val)
    (hn : 0 ≤ n.val) (hon : off.val + n.val ≤ L) (h1 : 0 ≤ a.hi.val) (h2 : a.hi.val ≤ L) :
    (rstopOf (ix 0) off n a).val = min a.hi.val (off.val + n.val) - off.val := by
  unfold rstopOf
  have e : (ix 0 + imin a.hi (off + n) - off).val = 0 + min a.hi.val (off.val + n.val) - off.val :=
    subv (addv ix0 (iminv rfl (addv rfl rfl (by omega) (by omega))) (by omega) (by omega)) rfl
      (by omega) (by omega)
  rw [e]; omega

theorem subAnns_labels (L : Int) (hL : L < 2 ^ 62) (off n p : JInt64) (h0 : 0 ≤ off.val)
    (hn : 0 ≤ n.val) (hon : off.val + n.val ≤ L) (hp1 : 1 ≤ p.val) (hpn : p.val ≤ n.val) :
    ∀ l : List RAnn, (∀ a ∈ l, InsideN L a) →
      ((subAnns (ix 0) off n l).filter (applies p)).map RAnn.label =
        (l.filter (applies (p + off))).map RAnn.label
  | [] => fun _ => rfl
  | a :: t => fun hl => by
    have ha := hl a (by simp)
    unfold InsideN at ha
    have ih := subAnns_labels L hL off n p h0 hn hon hp1 hpn t (fun b hb => hl b (by simp [hb]))
    have hO : (off + n).val = off.val + n.val := addv rfl rfl (by omega) (by omega)
    have hpo : (p + off).val = p.val + off.val := addv rfl rfl (by omega) (by omega)
    simp only [subAnns]
    split
    · rename_i hc
      have eU := rstart_val L hL off a h0 (by omega) ha.1 ha.2.1
      have eV := rstop_val L hL off n a h0 hn hon ha.2.2.1 ha.2.2.2
      have key : applies p (a.setR (urange (rstartOf (ix 0) off a) (rstopOf (ix 0) off n a))) =
          applies (p + off) a := by
        rw [applies_urange, eU, eV]
        unfold applies
        rw [hpo]
        exact decide_iff (by constructor <;> intro _ <;> omega)
      simp only [List.filter_cons, key]
      by_cases hq : applies (p + off) a = true <;> simp [hq, ih, RAnn.setR]
    · rename_i hc
      have key : applies (p + off) a = false := by
        unfold applies
        rw [hpo]
        exact decide_eq_false (by omega)
      simp only [List.filter_cons, key]
      simpa using ih

theorem subAnns_inside (L : Int) (hL : L < 2 ^ 62) (off n : JInt64) (h0 : 0 ≤ off.val)
    (hn : 0 ≤ n.val) (hon : off.val + n.val ≤ L) :
    ∀ l : List RAnn, (∀ a ∈ l, InsideN L a) → ∀ b ∈ subAnns (ix 0) off n l, InsideN n.val b
  | [] => fun _ b hb => by simp [subAnns] at hb
  | a :: t => fun hl b hb => by
    have ha := hl a (by simp)
    unfold InsideN at ha
    have ih := subAnns_inside L hL off n h0 hn hon t (fun b hb => hl b (by simp [hb]))
    have hO : (off + n).val = off.val + n.val := addv rfl rfl (by omega) (by omega)
    simp only [subAnns] at hb
    split at hb
    · rename_i hc
      rcases List.mem_cons.mp hb with rfl | hb
      · have eU := rstart_val L hL off a h0 (by omega) ha.1 ha.2.1
        have eV := rstop_val L hL off n a h0 hn hon ha.2.2.1 ha.2.2.2
        obtain ⟨hlo, hhi⟩ := setR_urange a (rstartOf (ix 0) off a) (rstopOf (ix 0) off n a)
        unfold InsideN
        rw [hlo, eU]
        rcases hhi with ⟨hhi, _⟩ | ⟨hhi, _⟩ <;> rw [hhi] <;> omega
      · exact ih b hb
    · exact ih b hb

/-- `AnnotatedString(ss)` for a SubString `ss` of `x` holds the SubString's bytes,
at each of its code units the annotations of `x` at the same code unit apply, in
order, and all its regions lie inside `1:ncodeunits(ss)`. Precondition: the
regions of `x` lie inside `1:ncodeunits(x)`. -/
def SubConvert : Prop :=
  ∀ (x : AStr) (off n : JInt64), RegionsInside x → 0 ≤ off.val → 0 ≤ n.val →
    off.val + n.val ≤ x.str.bytes.length →
    ∃ z, annotatedStringOfSub ⟨x, off, n⟩ = .ok z ∧
      z.str.bytes = (x.str.bytes.drop off.val.toNat).take n.val.toNat ∧
      (∀ p : JInt64, 1 ≤ p.val → p.val ≤ n.val → labelsAt z p = labelsAt x (p + off)) ∧
      RegionsInside z

theorem subConvert_proven : SubConvert := by
  intro x off n hx h0 hn hon
  have hL := x.str.small
  have hr : asLoop [.sub ⟨x, off, n⟩] [] [] =
      ((x.str.bytes.drop off.val.toNat).take n.val.toNat, subAnns (ix 0) off n x.anns) := by
    simp [asLoop, subBytes, JSub.view, JStr.slice]
  have hlen : ((x.str.bytes.drop off.val.toNat).take n.val.toNat).length < 2 ^ 62 :=
    slice_small x.str _ _
  have hz : annotatedStringOfSub ⟨x, off, n⟩ = .ok ⟨⟨_, hlen⟩, subAnns (ix 0) off n x.anns⟩ := by
    simp only [annotatedStringOfSub, annotatedstring, hr]
    rw [dif_pos hlen]
  refine ⟨_, hz, rfl, ?_, ?_⟩
  · intro p hp1 hpn
    rw [labelsAt_eq, labelsAt_eq]
    exact subAnns_labels x.str.bytes.length (by omega) off n p h0 hn hon hp1 hpn x.anns hx
  · intro b hb
    have hzl : ((((x.str.bytes.drop off.val.toNat).take n.val.toNat).length : Nat) : Int) = n.val := by
      simp only [List.length_take, List.length_drop]; omega
    have := subAnns_inside x.str.bytes.length (by omega) off n h0 hn hon x.anns hx b hb
    show InsideN (((x.str.bytes.drop off.val.toNat).take n.val.toNat).length : Nat) b
    rw [hzl]
    exact this

theorem mem_annsRange (r : Region) : ∀ (l : List RAnn) (b : RAnn), b ∈ annsRange r l →
    r.1.val ≤ b.lo.val ∧ b.lo.val ≤ b.hi.val ∧ b.hi.val ≤ r.2.val
  | [], b, hb => by simp [annsRange] at hb
  | a :: t, b, hb => by
    simp only [annsRange] at hb
    split at hb
    · rename_i hne
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [isemptyR_urange, imax_val, imin_val] at hne
        have hne' : ¬ (min r.2.val a.hi.val < max r.1.val a.lo.val) := by
          intro h; rw [decide_eq_true h] at hne; exact absurd hne (by decide)
        obtain ⟨hlo, hhi⟩ := setR_urange a (imax r.1 a.lo) (imin r.2 a.hi)
        rw [hlo, imax_val]
        rcases hhi with ⟨hhi, _⟩ | ⟨_, hlt⟩
        · rw [hhi, imin_val]; omega
        · rw [imax_val, imin_val] at hlt; omega
      · exact mem_annsRange r t b hb
    · exact mem_annsRange r t b hb

/-- The regions `annotations(ss)` returns for a SubString `ss` lie inside
`1:ncodeunits(ss)`, whatever the regions of the parent. -/
def SubAnnotationsInside : Prop :=
  ∀ (x : AStr) (off n : JInt64), 0 ≤ off.val → 0 ≤ n.val → off.val + n.val ≤ x.str.bytes.length →
    ∀ b ∈ annotationsSub ⟨x, off, n⟩, 1 ≤ b.lo.val ∧ b.lo.val ≤ b.hi.val ∧ b.hi.val ≤ n.val

theorem subAnnotationsInside_proven : SubAnnotationsInside := by
  intro x off n h0 hn hon b hb
  have hL := x.str.small
  unfold annotationsSub annotationsRange at hb
  simp only [List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hr := mem_annsRange _ _ _ ha
  have e1 : (off + ix 1).val = off.val + 1 := addv rfl ix1 (by omega) (by omega)
  have e2 : (off + n).val = off.val + n.val := addv rfl rfl (by omega) (by omega)
  have hs := setR_urange a (off + ix 1) (off + n)
  have hfst : (urange (off + ix 1) (off + n)).1 = off + ix 1 := rfl
  have hsnd : (urange (off + ix 1) (off + n)).2 = (a.setR (urange (off + ix 1) (off + n))).hi := rfl
  rw [hfst, hsnd] at hr
  have e3 : (a.lo - off).val = a.lo.val - off.val := subv rfl rfl (by omega) (by omega)
  have e4 : (a.hi - off).val = a.hi.val - off.val := subv rfl rfl (by omega) (by omega)
  obtain ⟨hlo, hhi⟩ := setR_urange a (a.lo - off) (a.hi - off)
  rw [hlo, e3]
  rcases hhi with ⟨hhi, _⟩ | ⟨hhi, hlt⟩ <;> rw [hhi] <;> omega

/-! ## Refuted properties -/

/-- `"aé"`. -/
def strAE : JStr := ⟨[0x61, 0xc3, 0xa9], by decide⟩
/-- `"abcdef"`. -/
def strAbcdef : JStr := ⟨[0x61, 0x62, 0x63, 0x64, 0x65, 0x66], by decide⟩

/-- `reverse(x)` keeps each annotation on the same characters
(`base/strings/annotated.jl:32-35`): listing, for each character, the labels of
the annotations that apply to it, the list of `reverse(x)` is the reversed list
of `x`. -/
def ReverseKeepsChars : Prop :=
  ∀ x : AStr,
    (validIndices (areverse x).str).map (fun i => labelsAt (areverse x) (ix i)) =
      ((validIndices x.str).map (fun i => labelsAt x (ix i))).reverse

theorem reverseKeepsChars_refuted : ¬ ReverseKeepsChars := by
  intro h
  have := h ⟨strAE, [⟨ix 1, ix 1, 1⟩]⟩
  revert this; decide

/-- `annotations(ss, pos)` for a SubString `ss` returns the annotations of
`annotations(ss)` that overlap `pos`, clamped to `pos`, all in SubString
coordinates. -/
def SubAnnotationsPosRelative : Prop :=
  ∀ (x : AStr) (off n plo phi : JInt64), 0 ≤ off.val → 0 ≤ n.val →
    off.val + n.val ≤ x.str.bytes.length → 1 ≤ plo.val → plo.val ≤ phi.val → phi.val ≤ n.val →
    annotationsSubRange ⟨x, off, n⟩ (urange plo phi) =
      annsRange (urange plo phi) (annotationsSub ⟨x, off, n⟩)

theorem subAnnotationsPosRelative_refuted : ¬ SubAnnotationsPosRelative := by
  intro h
  have := h ⟨strAbcdef, [⟨ix 1, ix 6, 1⟩]⟩ (ix 2) (ix 2) (ix 1) (ix 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- `eachregion` of an empty AnnotatedString yields no regions, as `eachregion`
of an empty SubString of an AnnotatedString does. -/
def EachregionEmpty : Prop :=
  ∀ (x : AStr) (ss : ASub) (pos : Region), x.str.bytes = [] → ss.ncu.val = 0 →
    eachregion x (defaultRegion x) = eachregionSub ss pos

theorem eachregionEmpty_refuted : ¬ EachregionEmpty := by
  intro h
  let e : AStr := ⟨JStr.empty, []⟩
  have hs : eachregionSub ⟨e, ix 0, ix 0⟩ (ix 1, ix 0) = .ok [] := rfl
  have := (h e ⟨e, ix 0, ix 0⟩ (ix 1, ix 0) rfl rfl).trans hs
  exact ok_ne _ [] (fun l => l.isEmpty) rfl (by decide) this

/-! ## Registry -/

def annotatedEntries : List Entry := [
  { id := "stringutil-annotated-reverse"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["reverse(::AnnotatedString)", "annotations(::AnnotatedString, ::Integer)"]
    statement := "For every AnnotatedString x, the labels applying to each character of reverse(x) (over the valid indices of reverse(x).string) are those of x's characters in reverse order."
    source := "base/strings/annotated.jl:32-35 (AnnotatedString docstring: code should conserve which characters an annotation is applied to)"
    status := .refuted
    prop := ``ReverseKeepsChars
    thm := some ``reverseKeepsChars_refuted
    issue := "none found (queries: issues: reverse AnnotatedString, prs: reverse AnnotatedString, issues: AnnotatedString reverse annotations, issues: reverse annotated, issues: AnnotatedString region multibyte, issues: AnnotatedString (30 most relevant titles read))"
    notes := "reverse(AnnotatedString(\"aé\", [(1:1, :A, 1)])) is \"éa\" with region 2:2, a continuation byte, so neither character carries :A. Regions are reflected with lastindex(s) instead of ncodeunits(s) and per byte instead of per character (base/strings/annotated.jl:346-355)." },
  { id := "stringutil-annotated-substring-pos"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["annotations(::SubString{<:AnnotatedString}, ::UnitRange)", "annotations(::SubString{<:AnnotatedString}, ::Integer)", "annotations(::SubString{<:AnnotatedString})"]
    statement := "For a SubString ss of an AnnotatedString and a nonempty pos inside 1:ncodeunits(ss), annotations(ss, pos) equals the annotations of annotations(ss) that overlap pos, clamped to pos, in SubString coordinates."
    source := "base/strings/annotated.jl:402-417 (annotations docstring); invariant: annotations(ss) uses SubString coordinates (base/strings/annotated.jl:420-430)"
    status := .refuted
    prop := ``SubAnnotationsPosRelative
    thm := some ``subAnnotationsPosRelative_refuted
    issue := "none found (queries: issues: annotations SubString position, issues: annotations SubString offset, issues: annotations SubString, prs: annotations SubString, issues: AnnotatedString (30 most relevant titles read))"
    notes := "AnnotatedString(\"abcdef\", [(1:6, :A, 1)]), ss = SubString(s, 3, 4), pos = 1:2: annotations(ss, pos) has region 3:4 (parent coordinates) while annotations(ss) has 1:2. base/strings/annotated.jl:447-451 do not subtract s.offset." },
  { id := "stringutil-eachregion-empty"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["eachregion(::AnnotatedString)", "eachregion(::SubString{<:AnnotatedString})"]
    statement := "eachregion of an empty AnnotatedString (default subregion firstindex:lastindex = 1:0) yields no regions, as eachregion of an empty SubString of an AnnotatedString does."
    source := "base/strings/annotated.jl:542-543 (intended early return for an empty string) and the SubString method base/strings/annotated.jl:575-578"
    status := .refuted
    prop := ``EachregionEmpty
    thm := some ``eachregionEmpty_refuted
    issue := "none found (queries: issues: eachregion empty, prs: eachregion empty, issues: eachregion, prs: eachregion)"
    notes := "eachregion(AnnotatedString(\"\")) yields the single region 1:0: `isempty(s) || isempty(subregion) && return ...` parses as `isempty(s) || (isempty(subregion) && return ...)`." },
  { id := "stringutil-annotated-concat"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["annotatedstring(::AnnotatedString, ::AnnotatedString)", "annotations(::AnnotatedString, ::Integer)"]
    statement := "For AnnotatedStrings x and y whose regions lie inside 1:ncodeunits, annotatedstring(x, y) has the bytes of x followed by those of y, and at every code unit p the labels applying are those of x at p (p <= ncodeunits(x)) or of y at p - ncodeunits(x), in order."
    source := "base/strings/annotated.jl:32-35 (AnnotatedString docstring: conserve which characters an annotation applies to and the order of annotations)"
    status := .proven
    prop := ``ConcatLabels
    thm := some ``concatLabels_proven
    notes := "Needs the regions inside 1:ncodeunits: region.+size wraps for regions near typemax(Int), and a region of x reaching past ncodeunits(x) applies to y's bytes too." },
  { id := "stringutil-annotated-substring-convert"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["AnnotatedString(::SubString{<:AnnotatedString})", "annotatedstring(::SubString{<:AnnotatedString})"]
    statement := "For x whose regions lie inside 1:ncodeunits(x) and a SubString ss (offset, ncu) with 0 <= offset and offset + ncu <= ncodeunits(x), AnnotatedString(ss) has the bytes of ss, at each code unit p in 1:ncu the labels of x at p + offset apply, in order, and all its regions lie inside 1:ncu."
    source := "base/strings/annotated.jl:32-35 (AnnotatedString docstring); base/strings/annotated.jl:312"
    status := .proven
    prop := ``SubConvert
    thm := some ``subConvert_proven
    notes := "Index arithmetic (base/strings/annotated.jl:288-290) is modelled with wrapping Int; the bounds show it never wraps." },
  { id := "stringutil-annotated-substring-inside"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["annotations(::SubString{<:AnnotatedString})"]
    statement := "For any AnnotatedString x and SubString ss (offset, ncu) with 0 <= offset and offset + ncu <= ncodeunits(x), every region returned by annotations(ss) is nonempty and lies inside 1:ncu."
    source := "invariant: annotations(ss) returns regions relative to the SubString (base/strings/annotated.jl:420-430)"
    status := .proven
    prop := ``SubAnnotationsInside
    thm := some ``subAnnotationsInside_proven
    notes := "Holds for arbitrary parent regions, including ones outside the parent string." }
]

end JuliaLean.StringUtil
