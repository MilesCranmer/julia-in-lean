import JuliaLean.Reduce.Props
import JuliaLean.Float.Properties

/-!
Proof of `FindmaxAgree`: on `Float64` vectors, `findmax`/`findmin` return an element
`isequal` to `maximum`/`minimum`, with its 1-based index.
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

namespace FindmaxProof

section Generic

variable {β : Type}

/-- `m` is an element of `L` and no element of `L` is `lt`-greater than `m`. -/
def Maximal (lt : β → β → Bool) (m : β) (L : List β) : Prop :=
  m ∈ L ∧ ∀ z ∈ L, lt m z = false

/-- `op` selects one argument, never `lt`-below either argument, and `lt` is
negatively transitive, all on values satisfying `P`. -/
structure SelOp (P : β → Prop) (op : β → β → β) (lt : β → β → Bool) : Prop where
  sel : ∀ a b, P a → P b → op a b = a ∨ op a b = b
  left : ∀ a b, P a → P b → lt (op a b) a = false
  right : ∀ a b, P a → P b → lt (op a b) b = false
  ntrans : ∀ a b c, P a → P b → P c → lt a b = false → lt b c = false → lt a c = false

variable {P : β → Prop} {op : β → β → β} {lt : β → β → Bool}

theorem SelOp.irrefl (h : SelOp P op lt) (a : β) (ha : P a) : lt a a = false := by
  have hl := h.left a a ha ha
  rcases h.sel a a ha ha with e | e <;> rw [e] at hl <;> exact hl

theorem maximal_single (h : SelOp P op lt) (a : β) (ha : P a) : Maximal lt a [a] := by
  refine ⟨List.mem_singleton_self a, ?_⟩
  intro z hz
  rw [List.mem_singleton] at hz
  rw [hz]
  exact h.irrefl a ha

theorem maximal_append (h : SelOp P op lt) {m1 m2 : β} {L1 L2 : List β}
    (h1 : Maximal lt m1 L1) (h2 : Maximal lt m2 L2) (hP : ∀ z ∈ L1 ++ L2, P z) :
    Maximal lt (op m1 m2) (L1 ++ L2) := by
  have p1 : P m1 := hP m1 (List.mem_append_left _ h1.1)
  have p2 : P m2 := hP m2 (List.mem_append_right _ h2.1)
  have pm : P (op m1 m2) := by
    rcases h.sel m1 m2 p1 p2 with e | e <;> rw [e] <;> assumption
  refine ⟨?_, ?_⟩
  · rcases h.sel m1 m2 p1 p2 with e | e <;> rw [e]
    · exact List.mem_append_left _ h1.1
    · exact List.mem_append_right _ h2.1
  · intro z hz
    have pz := hP z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact h.ntrans _ _ _ pm p1 pz (h.left m1 m2 p1 p2) (h1.2 z hz)
    · exact h.ntrans _ _ _ pm p2 pz (h.right m1 m2 p1 p2) (h2.2 z hz)

theorem maximal_pair (h : SelOp P op lt) (a b : β) (ha : P a) (hb : P b) :
    Maximal lt (op a b) [a, b] :=
  maximal_append (L1 := [a]) (L2 := [b]) h (maximal_single h a ha) (maximal_single h b hb)
    (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)

theorem maximal_foldl (h : SelOp P op lt) :
    ∀ (rest L : List β) (m : β), Maximal lt m L → (∀ z ∈ L ++ rest, P z) →
      Maximal lt (rest.foldl (fun v x => op v (id x)) m) (L ++ rest)
  | [], L, m, hm, _ => by simpa using hm
  | x :: rest, L, m, hm, hP => by
    rw [List.foldl_cons]
    have e : L ++ x :: rest = (L ++ [x]) ++ rest := by simp
    rw [e] at hP ⊢
    apply maximal_foldl h rest (L ++ [x]) (op m (id x)) _ hP
    exact maximal_append h hm (maximal_single h x (hP x (by simp)))
      (fun z hz => hP z (List.mem_append_left _ hz))

theorem maximal_mrImpl (h : SelOp P op lt) (blk : Nat) :
    ∀ (n : Nat) (a : β) (rest : List β), rest.length ≤ n → (∀ z ∈ a :: rest, P z) →
      Maximal lt (mrImpl id op id blk a rest) (a :: rest) := by
  intro n
  induction n with
  | zero =>
    intro a rest hl hP
    cases rest with
    | nil => rw [mrImpl]; exact maximal_single h a (hP a (by simp))
    | cons b r => simp at hl
  | succ n ih =>
    intro a rest hl hP
    cases rest with
    | nil => rw [mrImpl]; exact maximal_single h a (hP a (by simp))
    | cons b rest' =>
      rw [mrImpl]
      split
      · have hm := maximal_foldl h rest' [a, b] (op (id a) (id b))
          (maximal_pair h a b (hP a (by simp)) (hP b (by simp))) (by simpa using hP)
        simpa using hm
      · split
        · rename_i hd
          have := congrArg List.length hd
          simp only [List.length_drop, List.length_cons, List.length_nil] at this
          omega
        · rename_i c rest2 hd
          have hsplit : a :: b :: rest' =
              (a :: (b :: rest').take ((rest'.length + 1) / 2)) ++ (c :: rest2) := by
            rw [← hd, List.cons_append, List.take_append_drop]
          have hlen := congrArg List.length hd
          simp only [List.length_drop, List.length_cons] at hlen hl
          rw [hsplit] at hP ⊢
          apply maximal_append h _ _ hP
          · apply ih
            · simp only [List.length_take, List.length_cons]; omega
            · exact fun z hz => hP z (List.mem_append_left _ hz)
          · apply ih
            · omega
            · exact fun z hz => hP z (List.mem_append_right _ hz)

theorem maximal_mapreduceArr (h : SelOp P op lt) (e : R β) (blk : Nat) (L : List β)
    (hne : L ≠ []) (hP : ∀ z ∈ L, P z) :
    ∃ m, mapreduceArr id op id e blk L = .ok m ∧ Maximal lt m L := by
  match L, hne with
  | [], hne => exact absurd rfl hne
  | [a], _ => exact ⟨a, rfl, maximal_single h a (hP a (by simp))⟩
  | a :: b :: rest, _ =>
    simp only [mapreduceArr]
    split
    · refine ⟨_, rfl, ?_⟩
      have hm := maximal_foldl h rest [a, b] (op (id a) (id b))
        (maximal_pair h a b (hP a (by simp)) (hP b (by simp))) (by simpa using hP)
      simpa using hm
    · exact ⟨_, rfl, maximal_mrImpl h blk _ a (b :: rest) (Nat.le_refl _) hP⟩

theorem maximal_mapfoldlNoInit (h : SelOp P op lt) (e : R β) (L : List β)
    (hne : L ≠ []) (hP : ∀ z ∈ L, P z) :
    ∃ m, mapfoldlNoInit id op id e L = .ok m ∧ Maximal lt m L := by
  match L, hne with
  | [], hne => exact absurd rfl hne
  | a :: rest, _ =>
    refine ⟨_, rfl, ?_⟩
    exact maximal_foldl h rest [a] (id a) (maximal_single h a (hP a (by simp))) hP

end Generic

theorem zipIdx_getElem? {α : Type} :
    ∀ (l : List α) (k : Nat) (p : α × Nat), p ∈ l.zipIdx k → k ≤ p.2 ∧ l[p.2 - k]? = some p.1
  | [], _, _, hp => by simp at hp
  | x :: l, k, p, hp => by
    have e : (x :: l).zipIdx k = (x, k) :: l.zipIdx (k + 1) := rfl
    rw [e] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have ⟨hk, ih⟩ := zipIdx_getElem? l (k + 1) p hp
      refine ⟨by omega, ?_⟩
      have : p.2 - k = (p.2 - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      exact ih

theorem mem_zipIdx_fst {α : Type} :
    ∀ (l : List α) (k : Nat) (z : α), z ∈ l → ∃ q ∈ l.zipIdx k, q.1 = z
  | [], _, _, hz => by simp at hz
  | x :: l, k, z, hz => by
    have e : (x :: l).zipIdx k = (x, k) :: l.zipIdx (k + 1) := rfl
    rw [e]
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨(z, k), List.mem_cons_self .., rfl⟩
    · have ⟨q, hq, hq1⟩ := mem_zipIdx_fst l (k + 1) z hz
      exact ⟨q, List.mem_cons_of_mem _ hq, hq1⟩

theorem isless_irrefl (x : F64) : F64.isless x x = false := by
  cases hx : F64.isnan x <;> cases sx : F64.signbit x <;> simp [F64.isless, hx, sx]

theorem isless_asymm (x y : F64) (h : F64.isless x y = true) : F64.isless y x = false := by
  cases hx : F64.isnan x <;> cases hy : F64.isnan y <;>
    cases sx : F64.signbit x <;> cases sy : F64.signbit y <;>
    simp only [F64.isless, hx, hy, sx, sy] at h ⊢ <;>
    simp_all <;> omega

theorem isless_ntrans (x y z : F64) (h1 : F64.isless x y = false) (h2 : F64.isless y z = false) :
    F64.isless x z = false := by
  cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> cases hz : F64.isnan z <;>
    cases sx : F64.signbit x <;> cases sy : F64.signbit y <;> cases sz : F64.signbit z <;>
    simp only [F64.isless, hx, hy, hz, sx, sy, sz] at h1 h2 ⊢ <;>
    simp_all <;> omega

theorem signbit_true (x : F64) : F64.signbit x = true ↔ F64.toBits x ≥ 2 ^ 63 := by
  simp [F64.signbit]

theorem signbit_false (x : F64) : F64.signbit x = false ↔ F64.toBits x < 2 ^ 63 := by
  simp [F64.signbit]

theorem iszero_true (x : F64) : F64.iszero x = true ↔ F64.toBits x % 2 ^ 63 = 0 := by
  simp only [F64.iszero, F64.abs, F64.ofBits, F64.toBits, BitVec.toNat_ofNat, beq_iff_eq]
  constructor <;> intro h <;> omega

theorem iszero_false (x : F64) : F64.iszero x = false ↔ F64.toBits x % 2 ^ 63 ≠ 0 := by
  constructor
  · intro h h0
    have := (iszero_true x).mpr h0
    rw [h] at this
    exact Bool.noConfusion this
  · intro h
    cases hz : F64.iszero x with
    | false => rfl
    | true => exact absurd ((iszero_true x).mp hz) h

theorem fisless_eq (x y : F64) (hx : F64.isnan x = false) (hy : F64.isnan y = false) :
    Val.fisless x y = F64.isless x y := by
  have bx : F64.toBits x < 2 ^ 64 := x.isLt
  have bY : F64.toBits y < 2 ^ 64 := y.isLt
  cases sx : F64.signbit x <;> cases sy : F64.signbit y <;>
    cases zx : F64.iszero x <;> cases zy : F64.iszero y <;>
    simp only [Val.fisless, F64.lt, F64.isless, hx, hy, sx, sy, zx, zy] <;>
    simp_all [signbit_true, signbit_false, iszero_true, iszero_false] <;> omega

/-- `isgreater` on `Float64`, `base/operators.jl:295`. -/
def fgt (x y : F64) : Bool :=
  if F64.isnan x || F64.isnan y then F64.isless x y else F64.isless y x

theorem fgt_ntrans (x y z : F64) (h1 : fgt x y = false) (h2 : fgt y z = false) :
    fgt x z = false := by
  cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> cases hz : F64.isnan z <;>
    simp [fgt, hx, hy, hz] at h1 h2 ⊢ <;>
    first
    | exact isless_ntrans _ _ _ h2 h1
    | simp_all [F64.isless]

theorem fgt_isequal (x y : F64) (h1 : fgt x y = false) (h2 : fgt y x = false) :
    F64.isequal x y = true := by
  have hp := (islessPartition_proven x y).2
  cases hx : F64.isnan x <;> cases hy : F64.isnan y <;>
    simp [fgt, hx, hy] at h1 h2 <;>
    first
    | exact hp.mpr ⟨h2, h1⟩
    | simp_all [F64.isless, F64.isequal]

theorem vmax_f64 (x y : F64) : Val.vmax (.f64 x) (.f64 y) = .f64 (Val.fmax x y) := rfl

theorem vmin_f64 (x y : F64) : Val.vmin (.f64 x) (.f64 y) = .f64 (Val.fmin x y) := rfl

theorem visless_f64 (x y : F64) : Val.visless (.f64 x) (.f64 y) = F64.isless x y := rfl

theorem isgreater_f64 (x y : F64) : Vec.isgreater (.f64 x) (.f64 y) = fgt x y := rfl

theorem fmax_left (x y : F64) : F64.isless (Val.fmax x y) x = false := by
  unfold Val.fmax
  split
  · exact isless_irrefl x
  · rename_i hc
    cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> simp [hx, hy] at hc
    · rw [fisless_eq y x hy hx] at hc; exact hc
    · simp [F64.isless, hx, hy]

theorem fmax_right (x y : F64) : F64.isless (Val.fmax x y) y = false := by
  unfold Val.fmax
  split
  · rename_i hc
    cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> simp [hx, hy] at hc
    · rw [fisless_eq y x hy hx] at hc; exact isless_asymm y x hc
    · simp [F64.isless, hx]
    · simp [F64.isless, hx]
  · exact isless_irrefl y

theorem fmin_left (x y : F64) : fgt (Val.fmin x y) x = false := by
  unfold Val.fmin
  split
  · simp [fgt, isless_irrefl]
  · rename_i hc
    cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> simp [hx, hy] at hc
    · rw [fisless_eq x y hx hy] at hc; simp [fgt, hx, hy, hc]
    · simp [fgt, F64.isless, hx, hy]

theorem fmin_right (x y : F64) : fgt (Val.fmin x y) y = false := by
  unfold Val.fmin
  split
  · rename_i hc
    cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> simp [hx, hy] at hc
    · rw [fisless_eq x y hx hy] at hc; simp [fgt, hx, hy, isless_asymm x y hc]
    · simp [fgt, F64.isless, hx]
    · simp [fgt, F64.isless, hx]
  · simp [fgt, isless_irrefl]

theorem fmax_sel (x y : F64) : Val.fmax x y = x ∨ Val.fmax x y = y := by
  unfold Val.fmax; split <;> simp

theorem fmin_sel (x y : F64) : Val.fmin x y = x ∨ Val.fmin x y = y := by
  unfold Val.fmin; split <;> simp

/-- A `Float64` value. -/
def IsF (v : Val) : Prop := ∃ x, v = .f64 x

theorem maxSel : SelOp IsF Val.vmax Val.visless where
  sel := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [vmax_f64]; rcases fmax_sel x y with e | e <;> rw [e] <;> simp
  left := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [vmax_f64, visless_f64]; exact fmax_left x y
  right := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [vmax_f64, visless_f64]; exact fmax_right x y
  ntrans := by
    rintro a b c ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨z, rfl⟩
    simp only [visless_f64]; exact isless_ntrans x y z

theorem minSel : SelOp IsF Val.vmin Vec.isgreater where
  sel := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [vmin_f64]; rcases fmin_sel x y with e | e <;> rw [e] <;> simp
  left := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [vmin_f64, isgreater_f64]; exact fmin_left x y
  right := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [vmin_f64, isgreater_f64]; exact fmin_right x y
  ntrans := by
    rintro a b c ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨z, rfl⟩
    simp only [isgreater_f64]; exact fgt_ntrans x y z

theorem findmaxSel :
    SelOp (fun p : Val × Nat => IsF p.1)
      (fun (a b : Val × Nat) => if Val.visless a.1 b.1 then b else a)
      (fun p q => Val.visless p.1 q.1) where
  sel := by intro a b _ _; split <;> simp
  left := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨x, ha⟩ ⟨y, hb⟩
    simp only at ha hb; subst ha hb
    show Val.visless (if F64.isless x y then (Val.f64 y, j) else (Val.f64 x, i)).1 (.f64 x) = false
    split
    · rename_i hc; exact isless_asymm x y hc
    · exact isless_irrefl x
  right := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨x, ha⟩ ⟨y, hb⟩
    simp only at ha hb; subst ha hb
    show Val.visless (if F64.isless x y then (Val.f64 y, j) else (Val.f64 x, i)).1 (.f64 y) = false
    split
    · exact isless_irrefl y
    · rename_i hc
      show F64.isless x y = false
      simpa using hc
  ntrans := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨c, k⟩ ⟨x, ha⟩ ⟨y, hb⟩ ⟨z, hc⟩
    simp only at ha hb hc; subst ha hb hc
    exact isless_ntrans x y z

theorem findminSel :
    SelOp (fun p : Val × Nat => IsF p.1)
      (fun (a b : Val × Nat) => if Vec.isgreater a.1 b.1 then b else a)
      (fun p q => Vec.isgreater p.1 q.1) where
  sel := by intro a b _ _; split <;> simp
  left := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨x, ha⟩ ⟨y, hb⟩
    simp only at ha hb; subst ha hb
    show Vec.isgreater (if fgt x y then (Val.f64 y, j) else (Val.f64 x, i)).1 (.f64 x) = false
    split
    · rename_i hc
      show fgt y x = false
      cases hx : F64.isnan x <;> cases hy : F64.isnan y <;>
        simp [fgt, hx, hy] at hc ⊢ <;>
        first
        | exact isless_asymm _ _ hc
        | simp_all [F64.isless]
    · show fgt x x = false
      simp [fgt, isless_irrefl]
  right := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨x, ha⟩ ⟨y, hb⟩
    simp only at ha hb; subst ha hb
    show Vec.isgreater (if fgt x y then (Val.f64 y, j) else (Val.f64 x, i)).1 (.f64 y) = false
    split
    · show fgt y y = false
      simp [fgt, isless_irrefl]
    · rename_i hc
      show fgt x y = false
      simpa using hc
  ntrans := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨c, k⟩ ⟨x, ha⟩ ⟨y, hb⟩ ⟨z, hc⟩
    simp only at ha hb hc; subst ha hb hc
    exact fgt_ntrans x y z

theorem allF (v : List F64) : ∀ z ∈ v.map Val.f64, IsF z := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

theorem allF_zipIdx (v : List F64) :
    ∀ p ∈ (v.map Val.f64).zipIdx 1, IsF p.1 := by
  intro p hp
  have ⟨_, hg⟩ := zipIdx_getElem? _ _ p hp
  rw [List.getElem?_map] at hg
  cases hv : v[p.2 - 1]? with
  | none => rw [hv] at hg; simp at hg
  | some x =>
    rw [hv] at hg; simp at hg
    first | exact ⟨x, hg.symm⟩ | exact ⟨x, hg⟩

/-- The common argument for `findmax`/`maximum` and `findmin`/`minimum`. -/
theorem agree (v : List F64) (hv : v ≠ []) (lt : Val → Val → Bool) (opv : Val → Val → Val)
    (opp : Val × Nat → Val × Nat → Val × Nat) (lf : F64 → F64 → Bool)
    (hsv : SelOp IsF opv lt) (hsp : SelOp (fun p : Val × Nat => IsF p.1) opp (fun p q => lt p.1 q.1))
    (hlf : ∀ x y, lt (.f64 x) (.f64 y) = lf x y)
    (heq : ∀ x y, lf x y = false → lf y x = false → F64.isequal x y = true) :
    ∃ a b i, mapfoldlNoInit id opp id (.error .argumentError) ((v.map Val.f64).zipIdx 1) =
        .ok (.f64 a, i) ∧
      mapreduceArr id opv id (.error .argumentError) 1024 (v.map Val.f64) = .ok (.f64 b) ∧
      F64.isequal a b = true ∧ v[i - 1]? = some a := by
  have hne : v.map Val.f64 ≠ [] := by simpa using hv
  have hne2 : (v.map Val.f64).zipIdx 1 ≠ [] := by
    cases h : v.map Val.f64 with
    | nil => exact absurd h hne
    | cons x l => first | exact List.cons_ne_nil _ _ | simp | (intro h'; cases h')
  obtain ⟨m, hm, hmax⟩ := maximal_mapreduceArr hsv (.error .argumentError) 1024 _ hne (allF v)
  obtain ⟨p, hp, hpmax⟩ := maximal_mapfoldlNoInit hsp (.error .argumentError) _ hne2 (allF_zipIdx v)
  obtain ⟨b, rfl⟩ := allF v m hmax.1
  obtain ⟨a, ha⟩ := allF_zipIdx v p hpmax.1
  obtain ⟨p1, i⟩ := p
  simp only at ha
  subst ha
  refine ⟨a, b, i, hp, hm, ?_, ?_⟩
  · have ⟨q, hq, hq1⟩ := mem_zipIdx_fst (v.map Val.f64) 1 (.f64 b) hmax.1
    have h1 := hpmax.2 q hq
    simp only at h1
    rw [hq1, hlf] at h1
    have h2 := hmax.2 (.f64 a) (by
      have ⟨_, hg⟩ := zipIdx_getElem? _ _ _ hpmax.1
      exact List.mem_of_getElem? hg)
    rw [hlf] at h2
    exact heq a b h1 h2
  · have ⟨_, hg⟩ := zipIdx_getElem? _ _ _ hpmax.1
    simp only at hg
    rw [List.getElem?_map] at hg
    cases hv' : v[i - 1]? with
    | none => rw [hv'] at hg; simp at hg
    | some x => rw [hv'] at hg; simp at hg; rw [hg]

end FindmaxProof

open FindmaxProof in
theorem findmaxAgree_proven : FindmaxAgree := by
  intro v hv
  refine ⟨?_, ?_⟩
  · exact agree v hv Val.visless Val.vmax _ F64.isless maxSel findmaxSel visless_f64
      (fun x y h1 h2 => ((islessPartition_proven x y).2).mpr ⟨h1, h2⟩)
  · exact agree v hv Vec.isgreater Val.vmin _ fgt minSel findminSel isgreater_f64 fgt_isequal

end JuliaLean.Reduce
