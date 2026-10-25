import JuliaLean.Sockets.Model

namespace JuliaLean.Sockets

open JuliaLean

private theorem decimal_digit_table : ∀ d : Fin 10, digitVal (decCh d) = d := by decide +kernel
private theorem hex_digit_table : ∀ d : Fin 16, digitVal (hexCh d) = d := by decide +kernel

theorem digitVal_decCh {d : Nat} (h : d < 10) : digitVal (decCh d) = d :=
  decimal_digit_table ⟨d, h⟩

theorem digitVal_hexCh {d : Nat} (h : d < 16) : digitVal (hexCh d) = d :=
  hex_digit_table ⟨d, h⟩

theorem digit_not_ws {c : Char} (h : 0 ≤ digitVal c) : isWs c = false := by
  have hr : 48 ≤ c.toNat ∧ c.toNat ≤ 122 := by
    unfold digitVal at h
    split at h
    · omega
    · split at h
      · omega
      · split at h <;> omega
  simp (disch := omega) [isWs, JuliaLean.ParsePrint.IntParse.isZsZlZp]
  omega

theorem digit_not_sign {c : Char} (h : 0 ≤ digitVal c) : c ≠ '+' ∧ c ≠ '-' := by
  constructor <;> intro hc <;> subst c <;> simp [digitVal] at h

theorem dropWs_eq {cs : JStr} (h : ∀ c ∈ cs, isWs c = false) : dropWs cs = cs := by
  cases cs with
  | nil => rfl
  | cons c cs => simp [dropWs, h c (by simp)]

theorem dropLastWs_eq {cs : JStr} (h : ∀ c ∈ cs, isWs c = false) : dropLastWs cs = cs := by
  unfold dropLastWs
  rw [dropWs_eq]
  · simp
  · intro c hc
    exact h c (by simpa using hc)

theorem takeDigits_eq {base : Nat} {cs : JStr}
    (h : ∀ c ∈ cs, 0 ≤ digitVal c ∧ digitVal c < base) : takeDigits base cs = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [takeDigits, if_pos (h c (by simp))]
    rw [ih (fun c hc => h c (by simp [hc]))]

theorem numValGo_acc (base : Nat) (acc : Nat) (cs : JStr) :
    numValGo base acc cs = acc * base ^ cs.length + numValGo base 0 cs := by
  induction cs generalizing acc with
  | nil => simp [numValGo]
  | cons c cs ih =>
    simp only [numValGo, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc * base + (digitVal c).toNat), ih (digitVal c).toNat]
    simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc]

theorem numVal_cons (base : Nat) (c : Char) (cs : JStr) :
    numVal base (c :: cs) = (digitVal c).toNat * base ^ cs.length + numVal base cs := by
  simp only [numVal, numValGo, Nat.zero_mul, Nat.zero_add]
  exact numValGo_acc _ _ _

theorem numValGo_append (base : Nat) (acc : Nat) (l1 l2 : JStr) :
    numValGo base acc (l1 ++ l2) = numValGo base (numValGo base acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => rfl
  | cons c cs ih => exact ih (acc * base + (digitVal c).toNat)

theorem numVal_append (base : Nat) (l1 l2 : JStr) :
    numVal base (l1 ++ l2) = numVal base l1 * base ^ l2.length + numVal base l2 := by
  unfold numVal
  rw [numValGo_append, numValGo_acc]

theorem parseJInt_bare {base : Nat} {cs : JStr} (hne : cs ≠ [])
    (h : ∀ c ∈ cs, 0 ≤ digitVal c ∧ digitVal c < base)
    (hfit : (numVal base cs : Int) ≤ 9223372036854775807) :
    parseJInt base cs = .ok (numVal base cs) := by
  have hws : ∀ c ∈ cs, isWs c = false := fun c hc => digit_not_ws (h c hc).1
  have hd := dropWs_eq hws
  have ht := dropLastWs_eq hws
  have hr := takeDigits_eq h
  cases cs with
  | nil => contradiction
  | cons c cs =>
    have hsign := (digit_not_sign ((h c (by simp)).1)).1
    have hsign2 := (digit_not_sign ((h c (by simp)).1)).2
    have hnonneg : (0 : Int) ≤ numVal base (c :: cs) := by omega
    simp [parseJInt, hd, ht, hr, hsign, hsign2, hne, hfit, show
      ¬((numVal base (c :: cs) : Int) < -9223372036854775808) from by omega]

theorem repDigits_zero (base : Nat) (toCh : Nat → Char) (fuel : Nat) (acc : JStr) :
    repDigits base toCh fuel 0 acc = acc := by
  cases fuel <;> simp [repDigits]

theorem repDigits_value {base : Nat} (hb : 1 < base) (toCh : Nat → Char)
    (hch : ∀ d, d < base → digitVal (toCh d) = d) :
    ∀ fuel n acc, n ≤ fuel →
      numVal base (repDigits base toCh fuel n acc) = n * base ^ acc.length + numVal base acc := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc hn
    have hz : n = 0 := by omega
    simp [hz, repDigits]
  | succ fuel ih =>
    intro n acc hn
    by_cases h0 : n = 0
    · simp [h0, repDigits]
    · have hq : n / base < n := Nat.div_lt_self (by omega) hb
      have hqf : n / base ≤ fuel := by omega
      have hr : n % base < base := Nat.mod_lt _ (by omega)
      simp only [repDigits, if_neg h0]
      rw [ih _ _ hqf, numVal_cons, hch _ hr]
      simp only [Int.toNat_natCast, List.length_cons]
      have he : n / base * base + n % base = n := by
        simpa [Nat.mul_comm] using Nat.div_add_mod n base
      calc
        n / base * base ^ (acc.length + 1) + (n % base * base ^ acc.length + numVal base acc)
            = (n / base * base + n % base) * base ^ acc.length + numVal base acc := by
                simp [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
                  Nat.mul_left_comm, Nat.add_assoc]
        _ = _ := by rw [he]

theorem repDigits_mem {base : Nat} (hb : 0 < base) (toCh : Nat → Char)
    (hch : ∀ d, d < base → 0 ≤ digitVal (toCh d) ∧ digitVal (toCh d) < base) :
    ∀ fuel n acc, (∀ c ∈ acc, 0 ≤ digitVal c ∧ digitVal c < base) →
      ∀ c ∈ repDigits base toCh fuel n acc, 0 ≤ digitVal c ∧ digitVal c < base := by
  intro fuel
  induction fuel with
  | zero => intro n acc ha c hc; exact ha c hc
  | succ fuel ih =>
    intro n acc ha c hc
    by_cases h0 : n = 0
    · simpa [repDigits, h0] using ha c (by simpa [repDigits, h0] using hc)
    · simp only [repDigits, if_neg h0] at hc
      apply ih _ _ (fun x hx => ?_) c hc
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hch _ (Nat.mod_lt _ hb)
      · exact ha x hx

theorem repDigits_nonempty (base : Nat) (toCh : Nat → Char) :
    ∀ fuel n acc, acc ≠ [] → repDigits base toCh fuel n acc ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro n acc ha; exact ha
  | succ fuel ih =>
    intro n acc ha
    by_cases h0 : n = 0
    · simpa [repDigits, h0] using ha
    · simpa [repDigits, h0] using ih (n / base) (toCh (n % base) :: acc) (by simp)

theorem repDigits_head {base : Nat} (hb : 1 < base) (toCh : Nat → Char)
    (hinj : ∀ d, d < base → toCh d = toCh 0 → d = 0) :
    ∀ fuel n acc, 0 < n → n ≤ fuel → (repDigits base toCh fuel n acc).head? ≠ some (toCh 0) := by
  intro fuel
  induction fuel with
  | zero => intro n acc hp hf; omega
  | succ fuel ih =>
    intro n acc hp hf
    have h0 : n ≠ 0 := by omega
    have hq : n / base < n := Nat.div_lt_self hp hb
    simp only [repDigits, if_neg h0]
    by_cases hq0 : n / base = 0
    · rw [hq0, repDigits_zero]
      simp only [List.head?_cons]
      intro he
      have hz := hinj (n % base) (Nat.mod_lt _ (by omega)) (Option.some.inj he)
      have hv := Nat.div_add_mod n base
      rw [hq0] at hv
      simp only [Nat.mul_zero, Nat.zero_add] at hv
      omega
    · exact ih _ _ (Nat.zero_lt_of_ne_zero hq0) (by omega)

theorem repStr_value {base : Nat} (hb : 1 < base) (toCh : Nat → Char)
    (hch : ∀ d, d < base → digitVal (toCh d) = d) (n : Nat) :
    numVal base (repStr hb toCh n) = n := by
  by_cases h0 : n = 0
  · simp [repStr, h0, numVal, numValGo, hch 0 (by omega)]
  · simp only [repStr, if_neg h0]
    simpa [numVal, numValGo] using repDigits_value hb toCh hch n n [] (by omega)

theorem repStr_mem {base : Nat} (hb : 1 < base) (toCh : Nat → Char)
    (hch : ∀ d, d < base → digitVal (toCh d) = d) (n : Nat) :
    ∀ c ∈ repStr hb toCh n, 0 ≤ digitVal c ∧ digitVal c < base := by
  by_cases h0 : n = 0
  · intro c hc; simp [repStr, h0] at hc; subst c; rw [hch 0 (by omega)]; omega
  · simp only [repStr, if_neg h0]
    exact repDigits_mem (by omega) toCh (fun d hd => by rw [hch d hd]; omega) _ _ _ (by simp)

theorem repStr_nonempty {base : Nat} (hb : 1 < base) (toCh : Nat → Char) (n : Nat) :
    repStr hb toCh n ≠ [] := by
  cases n with
  | zero => simp [repStr]
  | succ n =>
    simp only [repStr, Nat.succ_ne_zero, if_false, repDigits]
    exact repDigits_nonempty _ _ _ _ _ (by simp)

@[simp] theorem decStr_value (n : Nat) : numVal 10 (decStr n) = n :=
  repStr_value (by decide) decCh (fun _ => digitVal_decCh) n

@[simp] theorem hexStr_value (n : Nat) : numVal 16 (hexStr n) = n :=
  repStr_value (by decide) hexCh (fun _ => digitVal_hexCh) n

theorem decStr_mem (n : Nat) : ∀ c ∈ decStr n, 0 ≤ digitVal c ∧ digitVal c < 10 :=
  repStr_mem (by decide) decCh (fun _ => digitVal_decCh) n

theorem hexStr_mem (n : Nat) : ∀ c ∈ hexStr n, 0 ≤ digitVal c ∧ digitVal c < 16 :=
  repStr_mem (by decide) hexCh (fun _ => digitVal_hexCh) n

@[simp] theorem decStr_nonempty (n : Nat) : decStr n ≠ [] :=
  repStr_nonempty (by decide) decCh n

@[simp] theorem hexStr_nonempty (n : Nat) : hexStr n ≠ [] :=
  repStr_nonempty (by decide) hexCh n

@[simp] theorem decStr_zero : decStr 0 = ['0'] := rfl
@[simp] theorem hexStr_zero : hexStr 0 = ['0'] := rfl

theorem decStr_head (n : Nat) (hn : 0 < n) : (decStr n).head? ≠ some '0' := by
  unfold decStr repStr
  rw [if_neg (by omega)]
  exact repDigits_head (by decide) decCh (fun d hd he => by
    have hv := congrArg digitVal he
    rw [digitVal_decCh hd, digitVal_decCh (by decide)] at hv
    omega) _ _ _ hn (by omega)

theorem decStr_leading (n : Nat) : ¬((decStr n).length > 1 ∧ (decStr n).head? = some '0') := by
  by_cases h0 : n = 0
  · simp [h0]
  · exact fun h => decStr_head n (by omega) h.2

@[simp] theorem parseJInt_hex {n : Nat} (hn : n < 65536) : parseJInt 16 (hexStr n) = .ok n := by
  simpa using parseJInt_bare (hexStr_nonempty n) (hexStr_mem n) (by simp; omega)

@[simp] theorem parseJInt_dec {n : Nat} (hn : n < 65536) : parseJInt 10 (decStr n) = .ok n := by
  simpa using parseJInt_bare (decStr_nonempty n) (decStr_mem n) (by simp; omega)

theorem digit_ne_sep {c sep : Char} (hc : 0 ≤ digitVal c) (hs : digitVal sep = -1) : c ≠ sep := by
  intro he; subst c; rw [hs] at hc; omega

@[simp] theorem colon_not_hex (n : Nat) : ':' ∉ hexStr n :=
  fun h => digit_ne_sep (hexStr_mem n ':' h).1 (by decide) rfl

@[simp] theorem dot_not_hex (n : Nat) : '.' ∉ hexStr n :=
  fun h => digit_ne_sep (hexStr_mem n '.' h).1 (by decide) rfl

@[simp] theorem colon_not_dec (n : Nat) : ':' ∉ decStr n :=
  fun h => digit_ne_sep (decStr_mem n ':' h).1 (by decide) rfl

@[simp] theorem dot_not_dec (n : Nat) : '.' ∉ decStr n :=
  fun h => digit_ne_sep (decStr_mem n '.' h).1 (by decide) rfl

theorem splitGo_app {sep : Char} {f : JStr} (rest rev : JStr)
    (h : sep ∉ f) : splitGo sep (f ++ rest) rev = splitGo sep rest (f.reverse ++ rev) := by
  induction f generalizing rev with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≠ sep := by intro he; apply h; simp [he]
    have hcs : sep ∉ cs := fun he => h (List.mem_cons_of_mem c he)
    simp only [List.cons_append, splitGo, show (c == sep) = false from beq_eq_false_iff_ne.mpr hc,
      Bool.false_eq_true, if_false]
    rw [ih (c :: rev) hcs]
    simp [List.reverse_cons, List.append_assoc]

theorem splitOn_noSep {sep : Char} {f : JStr} (h : sep ∉ f) : splitOn sep f = [f] := by
  unfold splitOn
  have he := splitGo_app (sep := sep) (f := f) [] [] h
  simpa [splitGo] using he

theorem splitOn_field {sep : Char} {f cs : JStr} (h : sep ∉ f) :
    splitOn sep (f ++ sep :: cs) = f :: splitOn sep cs := by
  unfold splitOn
  rw [splitGo_app (sep :: cs) [] h]
  simp [splitGo]

@[simp] theorem splitOn_hex (n : Nat) : splitOn ':' (hexStr n) = [hexStr n] :=
  splitOn_noSep (colon_not_hex n)

@[simp] theorem splitOn_dec (n : Nat) : splitOn '.' (decStr n) = [decStr n] :=
  splitOn_noSep (dot_not_dec n)

@[simp] theorem splitOn_hex_prefix (n : Nat) (cs : JStr) :
    splitOn ':' (hexStr n ++ ':' :: cs) = hexStr n :: splitOn ':' cs :=
  splitOn_field (colon_not_hex n)

@[simp] theorem splitOn_dec_prefix (n : Nat) (cs : JStr) :
    splitOn '.' (decStr n ++ '.' :: cs) = decStr n :: splitOn '.' cs :=
  splitOn_field (dot_not_dec n)

@[simp] theorem splitOn_colon_prefix (cs : JStr) :
    splitOn ':' (':' :: cs) = [] :: splitOn ':' cs := by simp [splitOn, splitGo]

@[simp] theorem splitOn_nil (sep : Char) : splitOn sep [] = [[]] := rfl

end JuliaLean.Sockets
