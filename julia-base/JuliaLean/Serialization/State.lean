import JuliaLean.Serialization.Basic

/-!
Agreement between the serializer's cycle table and the deserializer's backreference
table, and a small calculus `Dec` for decoders that read a known byte string.
-/

namespace JuliaLean.Serialization

open JuliaLean

/-- The serializer's table: distinct slots, all below the counter. -/
def Inv (es : ES) : Prop := (es.tab.map Prod.snd).Nodup ∧ ∀ p ∈ es.tab, p.2 < es.counter

theorem inv_init : Inv ES.init := by simp [Inv, ES.init]

theorem inv_register {es : ES} (h : Inv es) (key : Key) : Inv (es.register key) := by
  obtain ⟨hn, hb⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [ES.register, List.map_cons, List.nodup_cons]
    refine ⟨?_, hn⟩
    intro hm
    obtain ⟨p, hp, he⟩ := List.mem_map.1 hm
    have := hb p hp
    omega
  · intro p hp
    simp only [ES.register, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [ES.register]
    · have := hb p hp
      simp only [ES.register]
      omega

theorem encTable_register {es : ES} (h : Inv es) (key : Key) (k : Nat) :
    encTable (es.register key) k = if k = es.counter then some key else encTable es k := by
  unfold encTable ES.register
  by_cases hk : k = es.counter
  · subst hk
    simp
  · have : (es.counter == k) = false := by simp; omega
    simp [List.find?_cons, this, hk]

theorem encTable_ge {es : ES} (h : Inv es) {k : Nat} (hk : es.counter ≤ k) : encTable es k = none := by
  unfold encTable
  have : es.tab.find? (fun p => p.2 == k) = none := by
    rw [List.find?_eq_none]
    intro p hp
    have := h.2 p hp
    simp only [beq_iff_eq]
    omega
  simp [this]

theorem find_slot_of_mem {key : Key} {k : Nat} :
    ∀ l : List (Key × Nat), (l.map Prod.snd).Nodup → (key, k) ∈ l →
      l.find? (fun p => p.2 == k) = some (key, k)
  | [], _, h => by simp at h
  | q :: l, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 h with rfl | hm
    · simp
    · have hne : q.2 ≠ k := fun e => hn.1 (by rw [e]; exact List.mem_map_of_mem (f := Prod.snd) hm)
      have : (q.2 == k) = false := by simp [hne]
      simp [List.find?_cons, this, find_slot_of_mem l hn.2 hm]

theorem encTable_of_mem {es : ES} (h : Inv es) {key : Key} {k : Nat} (hm : (key, k) ∈ es.tab) :
    encTable es k = some key := by
  simp [encTable, find_slot_of_mem es.tab h.1 hm]

theorem lookup_mem {key : Key} {k : Nat} :
    ∀ l : List (Key × Nat), l.lookup key = some k → (key, k) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: l, h => by
    by_cases e : key = a
    · subst e
      simp [List.lookup] at h
      subst h
      simp
    · have : (key == a) = false := by simp [e]
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem l h)

theorem lt_of_mem {es : ES} (h : Inv es) {key : Key} {k : Nat} (hm : (key, k) ∈ es.tab) :
    k < es.counter := h.2 _ hm

/-! ### Agreement -/

/-- The deserializer's counter and table agree with the serializer, except on the
slots `E` that the deserializer has taken but not filled yet. -/
structure AgreeOn (E : List Nat) (es : ES) (ds : DS) : Prop where
  inv : Inv es
  counter : ds.counter = es.counter
  below : ∀ p ∈ E, p < es.counter
  nodup : E.Nodup
  table : ∀ k, ds.table k = if k ∈ E then none else encTable es k

theorem agree_init (io : Bytes) : AgreeOn [] ES.init (DS.init io) where
  inv := inv_init
  counter := rfl
  below := by simp
  nodup := List.nodup_nil
  table := by intro k; simp [DS.init, encTable, ES.init]

theorem AgreeOn.congr {E : List Nat} {es : ES} {ds ds' : DS} (h : AgreeOn E es ds)
    (hc : ds'.counter = ds.counter) (ht : ds'.table = ds.table) : AgreeOn E es ds' where
  inv := h.inv
  counter := by rw [hc, h.counter]
  below := h.below
  nodup := h.nodup
  table := by rw [ht]; exact h.table

/-- `resolve_ref_immediately`: the deserializer fills the slot the serializer registers. -/
theorem agree_resolve {E : List Nat} {es : ES} {ds : DS} (h : AgreeOn E es ds) (key : Key) :
    AgreeOn E (es.register key)
      { ds with counter := ds.counter + 1,
                table := fun j => if j = ds.counter then some key else ds.table j } where
  inv := inv_register h.inv key
  counter := by simp [ES.register, h.counter]
  below := fun p hp => by have := h.below p hp; simp [ES.register]; omega
  nodup := h.nodup
  table := by
    intro k
    rw [encTable_register h.inv]
    by_cases hk : k = es.counter
    · have hnot : k ∉ E := fun hm => by have := h.below k hm; omega
      subst hk
      simp [h.counter, hnot]
    · have : ¬ k = ds.counter := by rw [h.counter]; exact hk
      simp only [this, ↓reduceIte, hk, h.table k]

/-- `slot = s.counter; s.counter += 1` with the slot filled later. -/
theorem agree_push {E : List Nat} {es : ES} {ds : DS} (h : AgreeOn E es ds) (key : Key) :
    AgreeOn (es.counter :: E) (es.register key) { ds with counter := ds.counter + 1 } where
  inv := inv_register h.inv key
  counter := by simp [ES.register, h.counter]
  below := fun p hp => by
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [ES.register]
    · have := h.below p hp; simp [ES.register]; omega
  nodup := List.nodup_cons.2 ⟨fun hm => by have := h.below _ hm; omega, h.nodup⟩
  table := by
    intro k
    rw [encTable_register h.inv]
    by_cases hk : k = es.counter
    · have hnot : k ∉ E := fun hm => by have := h.below k hm; omega
      simp only [List.mem_cons, hk, true_or, ↓reduceIte]
      show ds.table es.counter = none
      rw [h.table, if_neg (by rw [← hk]; exact hnot), encTable_ge h.inv (Nat.le_refl _)]
    · simp only [List.mem_cons, hk, false_or, ↓reduceIte]
      exact h.table k

/-- `_setbackref!(s, p, x)` for a pending slot `p`. -/
theorem agree_fill {E : List Nat} {es : ES} {ds : DS} {p : Nat} {key : Key}
    (h : AgreeOn (p :: E) es ds) (hk : encTable es p = some key) :
    AgreeOn E es { ds with table := fun j => if j = p then some key else ds.table j } where
  inv := h.inv
  counter := h.counter
  below := fun q hq => h.below q (List.mem_cons_of_mem _ hq)
  nodup := (List.nodup_cons.1 h.nodup).2
  table := by
    have hp : p ∉ E := (List.nodup_cons.1 h.nodup).1
    intro k
    by_cases e : k = p
    · subst e; simp [hp, hk]
    · have := h.table k
      simp only [List.mem_cons, e, false_or] at this
      simp [e, this]

/-! ### Extension of the serializer state -/

/-- `es'` extends `es`: the counter only grows and earlier slots keep their keys. -/
def Pres (es es' : ES) : Prop :=
  es.counter ≤ es'.counter ∧ ∀ k, k < es.counter → encTable es' k = encTable es k

theorem pres_refl (es : ES) : Pres es es := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem pres_trans {a b c : ES} (h1 : Pres a b) (h2 : Pres b c) : Pres a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun k hk => by rw [h2.2 k (Nat.lt_of_lt_of_le hk h1.1), h1.2 k hk]⟩

theorem pres_register {es : ES} (h : Inv es) (key : Key) : Pres es (es.register key) :=
  ⟨by simp [ES.register], fun k hk => by rw [encTable_register h]; simp; omega⟩

/-! ### Decoders reading a known byte string -/

/-- Started in agreement `(E, es)` on a stream beginning with `bs`, the decoder `m`
returns `a`, consumes exactly `bs`, ends in agreement `(E', es')`, and leaves
`pending_refs` and `version` unchanged. -/
def Dec {α : Type} (m : Dm α) (E : List Nat) (es : ES) (bs : Bytes) (a : α)
    (E' : List Nat) (es' : ES) : Prop :=
  ∀ (ds : DS) (rest : Bytes), AgreeOn E es ds → ds.io = bs ++ rest →
    ∃ ds', m ds = .ok (a, ds') ∧ ds'.io = rest ∧ AgreeOn E' es' ds' ∧
      ds'.pending = ds.pending ∧ ds'.version = ds.version

theorem Dec.bind {α β : Type} {m : Dm α} {k : α → Dm β} {E E1 E2 : List Nat} {es es1 es2 : ES}
    {b1 b2 bs : Bytes} {a : α} {c : β}
    (h1 : Dec m E es b1 a E1 es1) (h2 : Dec (k a) E1 es1 b2 c E2 es2) (hb : bs = b1 ++ b2) :
    Dec (m >>= k) E es bs c E2 es2 := by
  intro ds rest ha hio
  rw [hb, List.append_assoc] at hio
  obtain ⟨ds1, r1, io1, a1, p1, v1⟩ := h1 ds (b2 ++ rest) ha hio
  obtain ⟨ds2, r2, io2, a2, p2, v2⟩ := h2 ds1 rest a1 io1
  exact ⟨ds2, by rw [bind_run r1, r2], io2, a2, by rw [p2, p1], by rw [v2, v1]⟩

theorem Dec.pure {α : Type} (a : α) (E : List Nat) (es : ES) :
    Dec (Pure.pure a : Dm α) E es [] a E es := by
  intro ds rest ha hio
  exact ⟨ds, pure_run a ds, by simpa using hio, ha, rfl, rfl⟩

theorem Dec.pure' {α : Type} {a b : α} (E : List Nat) (es : ES) (h : a = b) :
    Dec (Pure.pure a : Dm α) E es [] b E es := h ▸ Dec.pure a E es

theorem Dec.readU8 (b : UInt8) (E : List Nat) (es : ES) : Dec readU8 E es [b] b E es := by
  intro ds rest ha hio
  exact ⟨_, readU8_run hio, rfl, ha.congr rfl rfl, rfl, rfl⟩

theorem Dec.readN (bs : Bytes) (E : List Nat) (es : ES) : Dec (readN bs.length) E es bs bs E es := by
  intro ds rest ha hio
  exact ⟨_, readN_run hio, rfl, ha.congr rfl rfl, rfl, rfl⟩

theorem Dec.readLE (n m : Nat) (E : List Nat) (es : ES) :
    Dec (readLE n) E es (le n m) (m % 256 ^ n) E es := by
  intro ds rest ha hio
  exact ⟨_, readLE_run hio, rfl, ha.congr rfl rfl, rfl, rfl⟩

theorem Dec.readInt {t : IntTy} {x : Int} (hx : InRange t x) (E : List Nat) (es : ES) :
    Dec (readInt t) E es (le (nbytes t) (intBits t x)) x E es := by
  intro ds rest ha hio
  exact ⟨_, readInt_run hx hio, rfl, ha.congr rfl rfl, rfl, rfl⟩

theorem Dec.readChar {c : Nat} (hc : CharWF c) (E : List Nat) (es : ES) :
    Dec readChar E es (writeChar c) c E es := by
  intro ds rest ha hio
  exact ⟨_, readChar_run hc hio, rfl, ha.congr rfl rfl, rfl, rfl⟩

theorem Dec.stateless {α : Type} {m : Dm α} {E : List Nat} {es : ES} {a : α}
    (h : ∀ ds, m ds = .ok (a, ds)) : Dec m E es [] a E es := by
  intro ds rest ha hio
  exact ⟨ds, h ds, by simpa using hio, ha, rfl, rfl⟩

theorem Dec.resolveNow (key : Key) (E : List Nat) (es : ES) :
    Dec (resolveNow key) E es [] () E (es.register key) := by
  intro ds rest ha hio
  refine ⟨{ ds with counter := ds.counter + 1,
                    table := fun j => if j = ds.counter then some key else ds.table j },
    rfl, by simpa using hio, agree_resolve ha key, rfl, rfl⟩

theorem Dec.newSlot (key : Key) (E : List Nat) (es : ES) :
    Dec newSlot E es [] es.counter (es.counter :: E) (es.register key) := by
  intro ds rest ha hio
  refine ⟨{ ds with counter := ds.counter + 1 }, ?_, by simpa using hio, agree_push ha key, rfl, rfl⟩
  simp [Serialization.newSlot, ha.counter]

theorem Dec.setBackref {p : Nat} {key : Key} {E : List Nat} {es : ES}
    (hk : encTable es p = some key) : Dec (setBackref p key) (p :: E) es [] () E es := by
  intro ds rest ha hio
  exact ⟨_, rfl, by simpa using hio, agree_fill ha hk, rfl, rfl⟩

end JuliaLean.Serialization
