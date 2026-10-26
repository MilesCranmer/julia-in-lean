import JuliaLean.StringsCovB.Rx
import JuliaLean.RegexUnicode.CoreBasic

/-!
# Properties of the `base/regex.jl` and `base/pcre.jl` models
-/

namespace JuliaLean.StringsCovB.Rx

open JuliaLean JuliaLean.Strings
open JuliaLean.RegexUnicode.Core (Pcre Ovec RErr RJl)

/-! ## Flags and `show` -/

/-- The flag characters `a`, `i`, `m`, `s`, `x`. -/
def flagChars : List UInt32 := [0x61000000, 0x69000000, 0x6d000000, 0x73000000, 0x78000000]

/-- The 32 option pairs reachable from the defaults by the documented flags. -/
def reach : List (UInt32 × UInt32) :=
  (List.range 32).map fun b =>
    let co := DEFAULT_COMPILER_OPTS
    let co := if b &&& 1 != 0 then co ||| CASELESS else co
    let co := if b &&& 2 != 0 then co ||| MULTILINE else co
    let co := if b &&& 4 != 0 then co ||| DOTALL else co
    let co := if b &&& 8 != 0 then co ||| EXTENDED else co
    if b &&& 16 != 0 then (co &&& ~~~UCP &&& ~~~UTF &&& ~~~MATCH_INVALID_UTF, DEFAULT_MATCH_OPTS &&& ~~~NO_UTF_CHECK)
    else (co, DEFAULT_MATCH_OPTS)

/-- The option change of one documented flag. -/
def flagStep (f : UInt32) (p : UInt32 × UInt32) : UInt32 × UInt32 :=
  if f = 0x61000000 then (p.1 &&& ~~~UCP &&& ~~~UTF &&& ~~~MATCH_INVALID_UTF, p.2 &&& ~~~NO_UTF_CHECK)
  else if f = 0x69000000 then (p.1 ||| CASELESS, p.2)
  else if f = 0x6d000000 then (p.1 ||| MULTILINE, p.2)
  else if f = 0x73000000 then (p.1 ||| DOTALL, p.2)
  else (p.1 ||| EXTENDED, p.2)

theorem flagsLoop_cons (f : UInt32) (hf : f ∈ flagChars) (fs : List UInt32) (co mo : UInt32) :
    flagsLoop (f :: fs) co mo = flagsLoop fs (flagStep f (co, mo)).1 (flagStep f (co, mo)).2 := by
  simp only [flagChars, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
theorem reach_closed : ∀ p ∈ reach, ∀ f ∈ flagChars, flagStep f p ∈ reach := by
  decide +kernel

theorem reach_loop : ∀ fs, (∀ f ∈ fs, f ∈ flagChars) → ∀ p ∈ reach,
    ∃ q ∈ reach, flagsLoop fs p.1 p.2 = .ok q
  | [], _, p, hp => ⟨p, hp, rfl⟩
  | f :: fs, hfs, p, hp => by
    have hf := hfs f (List.mem_cons_self ..)
    rw [flagsLoop_cons f hf]
    exact reach_loop fs (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) _ (reach_closed p hp f hf)

/-- `true` when the flags printed by `show` rebuild `p`. -/
def rtCheck (p : UInt32 × UInt32) : Bool :=
  match showFlags p.1 p.2 with
  | some fl =>
    match flagsLoop fl DEFAULT_COMPILER_OPTS DEFAULT_MATCH_OPTS with
    | .ok q => q == p
    | .error _ => false
  | none => false

set_option maxRecDepth 100000 in
theorem reach_rt : ∀ p ∈ reach, rtCheck p = true := by decide +kernel

theorem reach_show (p : UInt32 × UInt32) (hp : p ∈ reach) : ∃ fl, showFlags p.1 p.2 = some fl ∧
    flagsLoop fl DEFAULT_COMPILER_OPTS DEFAULT_MATCH_OPTS = .ok p := by
  have h := reach_rt p hp
  unfold rtCheck at h
  split at h
  · rename_i fl hfl
    split at h
    · rename_i q hq
      exact ⟨fl, hfl, by rw [hq, beq_iff_eq.mp h]⟩
    · cases h
  · cases h

/-- Every `Regex(pattern, flags)` built from the documented flags `i`, `m`, `s`,
`x`, `a` is shown in the `r"..."flags` form, and those printed flags rebuild the
same compile and match options (`show` round-trips through `@r_str`). -/
def ShowFlagsRoundTrip : Prop :=
  ∀ (fs : List UInt32) (co mo : UInt32), (∀ f ∈ fs, f ∈ flagChars) →
    flagsLoop fs DEFAULT_COMPILER_OPTS DEFAULT_MATCH_OPTS = .ok (co, mo) →
    ∃ fl, showFlags co mo = some fl ∧ flagsLoop fl DEFAULT_COMPILER_OPTS DEFAULT_MATCH_OPTS = .ok (co, mo)

theorem showFlagsRoundTrip : ShowFlagsRoundTrip := by
  intro fs co mo hfs h
  obtain ⟨q, hq, he⟩ := reach_loop fs hfs (DEFAULT_COMPILER_OPTS, DEFAULT_MATCH_OPTS) (by decide)
  rw [he] at h
  cases h
  exact reach_show _ hq

/-- An unknown flag character makes `Regex(pattern, flags)` throw. -/
def UnknownFlagThrows : Prop :=
  ∀ f fs co mo, f ∉ flagChars → ∃ e, flagsLoop (f :: fs) co mo = .error e

theorem unknownFlagThrows : UnknownFlagThrows := by
  intro f fs co mo hf
  simp only [flagChars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf
  exact ⟨.str (.jl (.argumentError "unknown regex flag")), by simp [flagsLoop, h1, h2, h3, h4, h5]⟩

/-- `regex_opts_str` maps every subset of `imsx` to its letters in the order
`i`, `m`, `s`, `x`, so `wrap_string(r::Regex, unshared)` always finds its key. -/
def okIs {α : Type} [BEq α] (r : RJl α) (v : α) : Bool :=
  match r with
  | .ok x => x == v
  | .error _ => false

/-- The option bits of a subset `b` of `imsx`. -/
def optsOf (b : Nat) : UInt32 :=
  (if b &&& 1 != 0 then CASELESS else 0) ||| (if b &&& 2 != 0 then MULTILINE else 0) |||
    (if b &&& 4 != 0 then DOTALL else 0) ||| (if b &&& 8 != 0 then EXTENDED else 0)

/-- The letters of a subset `b` of `imsx`. -/
def lettersOf (b : Nat) : List UInt32 :=
  (if b &&& 1 != 0 then [0x69000000] else []) ++ (if b &&& 2 != 0 then [0x6d000000] else []) ++
    (if b &&& 4 != 0 then [0x73000000] else []) ++ (if b &&& 8 != 0 then [0x78000000] else [])

def OptsStrContract : Prop := ∀ b : Fin 16, okIs (regexOptsStr (optsOf b.val)) (lettersOf b.val) = true

theorem optsStrContract : OptsStrContract := by unfold OptsStrContract; decide +kernel

/-- `==` on `Regex` compares pattern and both option fields, and `hash` is a function
of exactly those fields, so equal regexes hash equally. -/
def RegexEqHash : Prop :=
  ∀ hs hu (a b : RegexObj) h, regexEq a b = true → hashRegex hs hu a h = hashRegex hs hu b h

theorem regexEqHash : RegexEqHash := by
  intro hs hu a b h e
  simp only [regexEq, Bool.and_eq_true, beq_iff_eq] at e
  obtain ⟨⟨h1, h2⟩, h3⟩ := e
  simp only [hashRegex, h1, h2, h3]

/-- In `*`, every `Regex` argument has the match options of the result, and
`*(r) = r`. -/
def MulContract : Prop :=
  (∀ mask args mo co shared res, mulOpts mask args mo co shared = .ok res →
    ∀ r, Arg.re r ∈ args → res.1 = some r.mopts ∨ mo = some r.mopts ∧ res.1 = mo) ∧
  (∀ r, mulOne r = r)

theorem mulOpts_mo (mask : UInt32) : ∀ args mo co shared res, mulOpts mask args mo co shared = .ok res →
    (∀ m, mo = some m → res.1 = some m) ∧ (∀ r, Arg.re r ∈ args → res.1 = some r.mopts)
  | [], mo, co, shared, res, h => by
    simp only [mulOpts, Except.ok.injEq] at h; subst h
    exact ⟨fun m hm => hm, fun r hr => by cases hr⟩
  | a :: rest, mo, co, shared, res, h => by
    cases a with
    | re r =>
      cases mo with
      | none =>
        simp only [mulOpts] at h
        have ih := mulOpts_mo mask rest _ _ _ res h
        refine ⟨fun m hm => (by cases hm), fun r' hr' => ?_⟩
        rcases List.mem_cons.mp hr' with e | e
        · cases e; exact ih.1 _ rfl
        · exact ih.2 r' e
      | some m =>
        simp only [mulOpts] at h
        split at h
        · rename_i hc
          have ih := mulOpts_mo mask rest _ _ _ res h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          refine ⟨fun m' hm => ih.1 m' hm, fun r' hr' => ?_⟩
          rcases List.mem_cons.mp hr' with e | e
          · cases e; rw [hc.1]; exact ih.1 m rfl
          · exact ih.2 r' e
        · cases h
    | str s =>
      simp only [mulOpts] at h
      have ih := mulOpts_mo mask rest _ _ _ res h
      exact ⟨ih.1, fun r hr => ih.2 r (by
        rcases List.mem_cons.mp hr with e | e
        · cases e
        · exact e)⟩
    | char c =>
      simp only [mulOpts] at h
      have ih := mulOpts_mo mask rest _ _ _ res h
      exact ⟨ih.1, fun r hr => ih.2 r (by
        rcases List.mem_cons.mp hr with e | e
        · cases e
        · exact e)⟩

theorem mulContract : MulContract :=
  ⟨fun mask args mo co shared res h r hr => Or.inl ((mulOpts_mo mask args mo co shared res h).2 r hr),
   fun _ => rfl⟩

/-! ## Match options -/

/-- A trivial compiled pattern and library for counterexamples: no capture groups,
no names, the primitive reporting no match. -/
def code0 : Code := ⟨RegexUnicode.Core.emptyAt [], 0, fun _ => .ok 0, [], fun _ => -49, 0⟩
def lib0 : Lib := ⟨fun _ _ => .ok code0, fun _ => some []⟩

/-- `true` unless the result is the "bad option value" error of `pcre2_match`. -/
def notBadOption {α : Type} : RJl α → Bool
  | .error (.errorException m) => m != "PCRE.exec error: bad option value"
  | _ => true

/-- Match options accepted by the `Regex` constructor (`match_options & ~EXECUTE_MASK == 0`)
are accepted by `pcre2_match`: the constructor's check is the documented way to
reject unusable options. -/
def ctorThenExec (lib : Lib) (pattern s : JStr) (copts mopts : Int) : Bool :=
  match regexCtor lib pattern copts mopts with
  | .ok re => match re.code with
    | some c => notBadOption (execC c s (ix 0) re.mopts)
    | none => true
  | .error _ => true

def MatchOptionsUsable : Prop :=
  ∀ (lib : Lib) (pattern s : JStr) (copts mopts : Int), ctorThenExec lib pattern s copts mopts = true

/-- `"a"`. -/
def jA : JStr := ⟨[0x61], by decide⟩

/-- `Regex("a", DEFAULT_COMPILER_OPTS, DEFAULT_MATCH_OPTS | PCRE.NO_START_OPTIMIZE)` is
accepted, and every match with it fails with "bad option value". -/
theorem matchOptionsUsable_refuted : ¬ MatchOptionsUsable := by
  intro h
  have := h lib0 jA jA DEFAULT_COMPILER_OPTS.toNat 0x40010000
  revert this
  decide +kernel

/-! ## Match data -/

theorem execR_run (c : Code) (s : JStr) (off : JInt64) (opts : UInt32) (w : World) :
    (execR c s off opts).run w = match execC c s off opts with
      | .ok r => .ok r.isSome ⟨(w.next :: w.live).erase w.next, w.next + 1, (w.next, r) :: w.ovecs⟩
      | .error e => .error e ⟨w.next :: w.live, w.next + 1, w.ovecs⟩ := by
  unfold execR exec liftR
  cases execC c s off opts <;> rfl

theorem execR_live (c : Code) (s : JStr) (off : JInt64) (opts : UInt32) (w w' : World) (b : Bool)
    (h : (execR c s off opts).run w = .ok b w') : w'.live = w.live := by
  rw [execR_run] at h
  split at h
  · cases h; simp
  · cases h

/-- `exec_r` frees the match data it allocates whenever it returns, so
`occursin`, `startswith` and `endswith` leave no match data behind. -/
def ExecRFrees : Prop :=
  (∀ c s off opts w w' b, (execR c s off opts).run w = .ok b w' → w'.live = w.live) ∧
  (∀ lib re s off w w' b, (occursinRe lib re s off).run w = .ok b w' → w'.live = w.live) ∧
  (∀ lib re s w w' b, (startswithRe lib s re).run w = .ok b w' → w'.live = w.live) ∧
  (∀ lib re s w w' b, (endswithRe lib s re).run w = .ok b w' → w'.live = w.live)

theorem liftR_bind_run {α β : Type} (x : RJl α) (k : α → PM β) (w : World) :
    (liftR x >>= k).run w = match x with
      | .ok p => (k p).run w
      | .error e => .error e w := by
  cases x <;> rfl

theorem compile_bind_live {α : Type} (lib : Lib) (re : RegexObj) (k : RegexObj × Code → PM α)
    (hk : ∀ p w w' a, (k p).run w = .ok a w' → w'.live = w.live) (w w' : World) (a : α)
    (h : (liftR (compileRegex lib re) >>= k).run w = .ok a w') : w'.live = w.live := by
  rw [liftR_bind_run] at h
  split at h
  · exact hk _ _ _ _ h
  · cases h

theorem execRFrees : ExecRFrees := by
  refine ⟨fun c s off opts w w' b h => execR_live c s off opts w w' b h, ?_, ?_, ?_⟩
  · intro lib re s off w w' b h
    exact compile_bind_live lib re _ (fun p w w' a h => execR_live _ _ _ _ w w' a h) w w' b h
  · intro lib re s w w' b h
    exact compile_bind_live lib re _ (fun p w w' a h => execR_live _ _ _ _ w w' a h) w w' b h
  · intro lib re s w w' b h
    exact compile_bind_live lib re _ (fun p w w' a h => execR_live _ _ _ _ w w' a h) w w' b h

/-- `true` when the allocated match-data blocks are those before the call, whether the
call returned or threw. -/
def liveSame {α : Type} (w : World) : EStateM.Result RErr World α → Bool
  | .ok _ w' => w'.live == w.live
  | .error _ w' => w'.live == w.live

/-- `match`, `findnext`, `occursin`, `startswith` and `endswith` free the match data
they allocate, including when `pcre2_match` reports an error (the match data is
C memory that the garbage collector does not reclaim). -/
def MatchDataFreed : Prop :=
  (∀ lib re s idx (w : World), liveSame w ((matchRe lib re s idx).run w) = true) ∧
  (∀ lib re s off (w : World), liveSame w ((occursinRe lib re s off).run w) = true)

/-- An empty world. -/
def w0 : World := ⟨[], 0, []⟩

/-- `match(r, "a", 0)` throws `InexactError` from the `Csize_t` conversion of the offset
`-1` after allocating the match data, which is never freed. -/
theorem matchDataFreed_refuted : ¬ MatchDataFreed := by
  intro h
  have := h.1 lib0 ⟨jA, DEFAULT_COMPILER_OPTS, DEFAULT_MATCH_OPTS, some code0⟩ jA (ix 0) w0
  revert this
  decide +kernel

/-! ## `RegexMatch` -/

/-- A match with the trivial pattern and the given captures. -/
def rmOf (caps : List (Option JSub)) : RM := ⟨⟨⟨jA, ix 0, ix 1⟩, caps, ix 1, []⟩, code0⟩

/-- `haskey(m, name)` answers for every name. -/
def HaskeyNameTotal : Prop := ∀ (m : RM) (name : List UInt8), ∃ b, haskeyName m name = .ok b

/-- `haskey(m, "a\0b")` throws `ArgumentError` from the `Cstring` conversion. -/
theorem haskeyNameTotal_refuted : ¬ HaskeyNameTotal := by
  intro h
  obtain ⟨b, hb⟩ := h (rmOf []) [0x61, 0, 0x62]
  revert hb
  simp [haskeyName, substringNumberFromName, cstring, bind, Except.bind]

/-- `haskey(m, i)` holds exactly when `m[i]` returns; `m[name]` returns only when
`haskey(m, name)`; iteration yields the captures in order and `length(m)` is their
number; `NamedTuple(m)` pairs the keys with the captures; `Dict(m)` has a value
for every key of `keys(m)`; `keys(m)` has one key per capture group. -/
def RegexMatchContract : Prop :=
  (∀ m i, haskeyIdx m i = true ↔ ∃ v, getindexIdx m i = .ok v) ∧
  (∀ m name v, getindexName m name = .ok v → haskeyName m name = .ok true) ∧
  (∀ m i, 1 ≤ i → i ≤ lengthM m → iterateM m i = some (m.m.captures.getD (i - 1) none, i + 1)) ∧
  (∀ m, iterateM m (lengthM m + 1) = none) ∧
  (∀ m ks, keysM m = .ok ks → ks.length = m.m.captures.length) ∧
  (∀ m nt, namedTupleM m = .ok nt → nt.map (·.2) = m.m.captures) ∧
  eltypeM (rmOf []) = "Union{Nothing, SubString{String}}"

theorem regexMatchContract : RegexMatchContract := by
  refine ⟨fun m i => ?_, fun m name v h => ?_, fun m i h1 h2 => ?_, fun m => ?_, fun m ks h => ?_,
    fun m nt h => ?_, rfl⟩
  · unfold haskeyIdx getindexIdx
    constructor
    · intro hi
      have hi' := of_decide_eq_true hi
      exact ⟨_, if_pos hi'⟩
    · intro ⟨v, hv⟩
      apply decide_eq_true
      by_cases hi : 1 ≤ i.val ∧ i.val ≤ m.m.captures.length
      · exact hi
      · rw [if_neg hi] at hv; cases hv
  · unfold getindexName at h
    unfold haskeyName
    cases hc : substringNumberFromName m.code name with
    | error e => rw [hc] at h; cases h
    | ok idx =>
      rw [hc] at h
      simp only [bind, Except.bind, pure, Except.pure] at h ⊢
      by_cases hp : idx ≤ 0
      · rw [if_pos hp] at h; cases h
      · simp only [Except.ok.injEq, decide_eq_true_eq]; omega
  · unfold lengthM at h2
    unfold iterateM
    rw [if_pos (show 1 ≤ i ∧ i ≤ m.m.captures.length from ⟨h1, h2⟩)]
  · unfold iterateM lengthM
    rw [if_neg (show ¬(1 ≤ m.m.captures.length + 1 ∧ m.m.captures.length + 1 ≤ m.m.captures.length) by omega)]
  · unfold keysM at h
    cases hc : captureNames m.code with
    | error e => rw [hc] at h; cases h
    | ok names =>
      rw [hc] at h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp
  · unfold namedTupleM at h
    cases hk : keysM m with
    | error e => rw [hk] at h; cases h
    | ok ks =>
      rw [hk] at h
      simp only [bind, Except.bind] at h
      have hl : ks.length = m.m.captures.length := by
        unfold keysM at hk
        cases hc : captureNames m.code with
        | error e => rw [hc] at hk; cases hk
        | ok names =>
          rw [hc] at hk
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hk
          subst hk; simp
      by_cases hd : ks.Nodup
      · rw [if_pos hd] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [List.map_snd_zip]; omega
      · rw [if_neg hd] at h; cases h

/-! ## `capture_names` -/

/-- One name-table entry of `entrySize` bytes: the big-endian group number, the
name and NUL padding. -/
def encodeEntry (entrySize : Nat) (e : Nat × List UInt8) : List UInt8 :=
  [UInt8.ofNat (e.1 >>> 8), UInt8.ofNat e.1] ++ e.2 ++ List.replicate (entrySize - 2 - e.2.length) 0

set_option maxRecDepth 100000 in
theorem or_shift_table : ∀ h < 256, ∀ l < 256, (h <<< 8 ||| l) = h * 256 + l := by decide +kernel

theorem be16 (k : Nat) (hk : k < 65536) :
    (UInt8.ofNat (k >>> 8)).toNat <<< 8 ||| (UInt8.ofNat k).toNat = k := by
  have u8 : ∀ n : Nat, (UInt8.ofNat n).toNat = n % 256 := fun n => by
    first | rfl | simp [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
  rw [u8, u8, Nat.shiftRight_eq_div_pow]
  have h1 : k / 2 ^ 8 % 256 = k / 256 := Nat.mod_eq_of_lt (by omega)
  rw [h1, or_shift_table (k / 256) (by omega) (k % 256) (by omega)]
  omega

theorem takeWhile_nz (n rest : List UInt8) (hn : 0 ∉ n) :
    (n ++ 0 :: rest).takeWhile (· != 0) = n := by
  induction n with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≠ 0 := fun h => hn (h ▸ List.mem_cons_self ..)
    have hxs : 0 ∉ xs := fun h => hn (List.mem_cons_of_mem _ h)
    simp [List.takeWhile_cons, hx, ih hxs]

/-- A name entry of a table `encodeEntry e ++ rest` at its start. -/
theorem nameEntry_encode (entrySize : Nat) (e : Nat × List UInt8) (rest : List UInt8)
    (hi : e.1 < 65536) (hn : 0 ∉ e.2) (hs : e.2.length + 3 ≤ entrySize) :
    nameEntry (encodeEntry entrySize e ++ rest) 1 = e := by
  obtain ⟨k, n⟩ := e
  simp only at hi hn hs
  have hpad : entrySize - 2 - n.length = (entrySize - 3 - n.length) + 1 := by omega
  simp only [nameEntry, encodeEntry, hpad, List.replicate_succ, List.cons_append, Nat.sub_self,
    List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero, List.append_assoc,
    List.nil_append]
  rw [takeWhile_nz _ _ hn, be16 k hi]

/-- Dropping whole entries of a table of equal-length entries. -/
theorem drop_flatMap_uniform {β : Type} (f : β → List UInt8) (size : Nat) :
    ∀ (es : List β) (i : Nat), (∀ e ∈ es, (f e).length = size) →
      (es.flatMap f).drop (i * size) = (es.drop i).flatMap f
  | [], i, _ => by simp
  | e :: es, 0, _ => by simp
  | e :: es, i + 1, h => by
    have hl := h e (List.mem_cons_self ..)
    have hs : i * size + size = (f e).length + i * size := by rw [hl]; omega
    rw [List.flatMap_cons, Nat.succ_mul, hs, List.drop_append, List.drop_eq_nil_of_le (by omega),
      List.nil_append, Nat.add_sub_cancel_left, List.drop_succ_cons]
    exact drop_flatMap_uniform f size es i (fun e he => h e (List.mem_cons_of_mem _ he))

theorem nameEntry_drop (tbl : List UInt8) (a : Nat) : nameEntry tbl (a + 1) = nameEntry (tbl.drop a) 1 := by
  simp only [nameEntry, Nat.add_sub_cancel, Nat.sub_self, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.drop_drop, Nat.add_zero]

/-- `capture_names(re)` decodes a name table: for a table made of entries with
group numbers below `2^16`, NUL-free names and an entry size leaving room for the
terminating NUL, the result maps each group number to its name (a later entry
for the same number wins, as `names[idx] = ...` does). -/
def CaptureNamesDecode : Prop :=
  ∀ (c : Code) (es : List (Nat × List UInt8)) (size : Nat),
    c.info INFO_NAMECOUNT = .ok es.length → c.info INFO_NAMEENTRYSIZE = .ok size →
    c.nametable = es.flatMap (encodeEntry size) →
    (∀ e ∈ es, e.1 < 65536 ∧ 0 ∉ e.2 ∧ e.2.length + 3 ≤ size) →
    captureNames c = .ok (es.foldl (fun d e => dictSet d e.1 e.2) [])

theorem encodeEntry_length (size : Nat) (e : Nat × List UInt8) (hs : e.2.length + 3 ≤ size) :
    (encodeEntry size e).length = size := by
  simp [encodeEntry]; omega

theorem captureNamesDecode : CaptureNamesDecode := by
  intro c es size hc hs ht hes
  simp only [captureNames, info, hc, hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
  have key : ∀ i, (hi : i < es.length) → nameEntry c.nametable (i * size + 1) = es[i] := by
    intro i hi
    have he := hes es[i] (List.getElem_mem hi)
    rw [ht, nameEntry_drop, drop_flatMap_uniform _ size es i (fun e h => encodeEntry_length size e (hes e h).2.2),
      List.drop_eq_getElem_cons hi, List.flatMap_cons]
    exact nameEntry_encode size _ _ he.1 he.2.1 he.2.2
  have : ∀ (n : Nat) (d : List (Nat × List UInt8)), n ≤ es.length →
      (List.range n).foldl (fun d i => dictSet d (nameEntry c.nametable (i * size + 1)).1
        (nameEntry c.nametable (i * size + 1)).2) d =
      (es.take n).foldl (fun d e => dictSet d e.1 e.2) d := by
    intro n
    induction n with
    | zero => intro d _; rfl
    | succ n ih =>
      intro d hn
      rw [List.range_succ, List.foldl_append, ih d (by omega), List.take_add_one, List.foldl_append,
        List.getElem?_eq_getElem (show n < es.length by omega)]
      simp only [List.foldl_cons, List.foldl_nil, Option.toList_some, key n (by omega)]
  rw [this es.length [] (Nat.le_refl _), List.take_length]

/-! ## Thread-local match contexts -/

/-- `get_local_match_context()` returns a non-null context, stores it at the slot of
the calling thread (`_tid() ≤ maxthreadid()`), and a second call on the same
thread returns the same context without allocating. -/
def LocalMatchContext : Prop :=
  ∀ (t m : Nat) (w : Ctxs), t < m →
    let r := getLocalMatchContext t m w
    r.1 ≠ 0 ∧ r.2.ctxs.getD t 0 = r.1 ∧ getLocalMatchContext t m r.2 = (r.1, r.2)

theorem growCtxs_len (t m : Nat) (w : Ctxs) (h : t ≤ w.ctxs.length + m) : t ≤ (growCtxs t m w).ctxs.length := by
  unfold growCtxs
  split
  · simp only [List.length_append, List.length_replicate]; omega
  · omega

theorem growCtxs_id (t m : Nat) (w : Ctxs) (h : t ≤ w.ctxs.length) : growCtxs t m w = w := by
  unfold growCtxs; rw [if_neg (by omega)]

theorem fetchCtx_spec (t : Nat) (w : Ctxs) (h : t < w.ctxs.length) :
    let r := fetchCtx (t + 1) w
    r.1 ≠ 0 ∧ r.2.ctxs.getD t 0 = r.1 ∧ t < r.2.ctxs.length ∧ fetchCtx (t + 1) r.2 = r := by
  by_cases h0 : w.ctxs.getD t 0 = 0
  · have e : fetchCtx (t + 1) w = (w.next + 1, { ctxs := w.ctxs.set t (w.next + 1), next := w.next + 2 }) := by
      simp only [fetchCtx, createMatchContext, Nat.add_sub_cancel, h0]; rfl
    have g : (w.ctxs.set t (w.next + 1)).getD t 0 = w.next + 1 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
    simp only [e]
    refine ⟨by omega, g, by simp [h], ?_⟩
    simp only [fetchCtx, Nat.add_sub_cancel, g]
    rw [if_neg (by omega)]
  · have e : fetchCtx (t + 1) w = (w.ctxs.getD t 0, w) := by
      simp only [fetchCtx, Nat.add_sub_cancel]; rw [if_neg h0]
    simp only [e]
    have h0' : ¬ w.ctxs[t] = 0 := by simpa [List.getD_eq_getElem?_getD, h] using h0
    simp [h, h0']

theorem localMatchContext : LocalMatchContext := by
  intro t m w htm
  simp only [getLocalMatchContext, tid, mth]
  have hl := growCtxs_len (t + 1) m w (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := fetchCtx_spec t (growCtxs (t + 1) m w) (by omega)
  refine ⟨h1, h2, ?_⟩
  rw [growCtxs_id (t + 1) m _ (by omega), h4]

/-! ## PCRE helpers -/

/-- `info` returns the answer of `pcre2_pattern_info` or raises one of its four
messages; `ovec_length` is twice the number of pairs; `err_message` raises for
`PCRE2_ERROR_BADDATA` and otherwise returns the bytes before the first NUL;
`jit_compile` is `true` on success and `false` for `PCRE2_ERROR_JIT_BADOPTION`;
`substring_length_bynumber` is `0` for an unset group; `free_re` and its kin
release the given object; `RegexMatch(..., offset::UInt, ...)` keeps an
offset that fits `Int`. -/
def PcreHelpersContract : Prop :=
  (∀ c what v, c.info what = .ok v → info c what = .ok v) ∧
  (∀ c what ret, c.info what = .error ret → ∃ m, info c what = .error (.errorException m)) ∧
  (∀ c, ovecLength c = 2 * (c.ncaps + 1)) ∧
  (∀ lib errno, lib.errmsg errno = none → ∃ e, errMessage lib errno = .error e) ∧
  (∀ lib errno bs, lib.errmsg errno = some bs → errMessage lib errno = .ok (bs.takeWhile (· != 0))) ∧
  (∀ lib c, c.jitRc = 0 → jitCompile lib c = .ok true) ∧
  (∀ lib c, c.jitRc = ERROR_JIT_BADOPTION → jitCompile lib c = .ok false) ∧
  (∀ lib c v k, 1 ≤ k → k ≤ c.ncaps → v.caps.getD (k - 1) none = none →
    substringLengthBynumber lib c v k = .ok 0) ∧
  (∀ live p, freeObj (p :: live) p = live) ∧
  (∀ mat caps (off : Int) offsets c, 0 ≤ off → off < 2 ^ 63 →
    (regexMatchCtor mat caps off offsets c).map (·.m.offset.val) = .ok off)

theorem pcreHelpersContract : PcreHelpersContract := by
  refine ⟨fun c what v h => by simp [info, h], fun c what ret h => by simp only [info, h]; exact ⟨_, rfl⟩, fun _ => rfl,
    fun lib errno h => by simp only [errMessage, h]; exact ⟨_, rfl⟩, fun lib errno bs h => by simp [errMessage, h],
    fun lib c h => by simp [jitCompile, h], fun lib c h => by simp [jitCompile, h, ERROR_JIT_BADOPTION],
    fun lib c v k h1 h2 h3 => ?_, fun live p => by simp [freeObj], fun mat caps off offsets c h1 h2 => ?_⟩
  · have hk : k ≠ 0 := by omega
    unfold substringLengthBynumber
    rw [if_neg hk, if_pos h2, h3]
  · simp only [regexMatchCtor, JInt.convert]
    rw [dif_pos ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
      by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩]
    rfl

/-! ## Constructor, `compile` and `show` -/

/-- `Regex(pattern, copts, mopts)` throws for options that are negative or do not fit
`UInt32`, and for compile or match options outside `COMPILE_MASK`/`EXECUTE_MASK`;
otherwise it keeps the pattern and options and compiles once: `compile` of a
compiled `Regex` returns it unchanged, and a pattern `pcre2_compile` rejects throws
`ErrorException`. `Regex(pattern)` and `r"..."` use the default options. `show` of a
`Regex` in the default form prints `r"`, the escaped pattern, `"` and the flags. -/
def RegexCtorContract : Prop :=
  (∀ lib p copts mopts, copts < 0 → ∃ e, regexCtor lib p copts mopts = .error e) ∧
  (∀ lib p copts mopts re, regexCtor lib p copts mopts = .ok re →
    re.pattern = p ∧ re.copts.toNat = copts ∧ re.mopts.toNat = mopts ∧ re.code.isSome) ∧
  (∀ lib re c, re.code = some c → compileRegex lib re = .ok (re, c)) ∧
  (∀ lib re errno erroff, re.code = none → lib.compile re.pattern.bytes re.copts = .error (errno, erroff) →
    ∃ e, compileRegex lib re = .error e) ∧
  (∀ lib p, regexDefault lib p = regexCtor lib p DEFAULT_COMPILER_OPTS.toNat DEFAULT_MATCH_OPTS.toNat ∧
    rStr lib p none = regexDefault lib p) ∧
  (∀ lib p f, rStr lib p (some f) = regexFlags lib p f) ∧
  (∀ escRaw showStr showU re fl, showFlags re.copts re.mopts = some fl →
    showRegex escRaw showStr showU re = "r\"".toUTF8.toList ++ escRaw re.pattern ++ "\"".toUTF8.toList ++ fl.flatMap charBytes)

theorem toU32_ok (x : Int) (u : UInt32) (h : toU32 x = .ok u) : (u.toNat : Int) = x := by
  unfold toU32 at h
  split at h
  · rename_i hx
    cases h
    change ((x.toNat % 4294967296 : Nat) : Int) = x
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · cases h

theorem regexCtorContract : RegexCtorContract := by
  refine ⟨fun lib p copts mopts h => ?_, fun lib p copts mopts re h => ?_,
    fun lib re c h => by simp [compileRegex, h], fun lib re errno erroff h1 h2 => ?_,
    fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, fun escRaw showStr showU re fl h => by simp [showRegex, h]⟩
  · unfold regexCtor toU32
    rw [if_neg (by omega)]
    exact ⟨_, rfl⟩
  · unfold regexCtor at h
    cases hc : toU32 copts with
    | error e => rw [hc] at h; cases h
    | ok co =>
      cases hm : toU32 mopts with
      | error e => rw [hc, hm] at h; cases h
      | ok mo =>
        rw [hc, hm] at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · split at h
          · cases h
          · cases hk : compileRegex lib ⟨p, co, mo, none⟩ with
            | error e => rw [hk] at h; cases h
            | ok pr =>
              rw [hk] at h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              unfold compileRegex at hk
              simp only at hk
              split at hk
              · cases hk
              · split at hk
                · cases hk
                · simp only [Except.ok.injEq] at hk
                  subst hk
                  exact ⟨rfl, toU32_ok _ _ hc, toU32_ok _ _ hm, rfl⟩
  · cases he : errMessage lib errno with
    | error e => exact ⟨e, by simp [compileRegex, h1, compileP, h2, he]⟩
    | ok m =>
      exact ⟨.errorException s!"PCRE compilation error: {String.fromUTF8! ⟨m.toArray⟩} at offset {erroff}",
        by simp [compileRegex, h1, compileP, h2, he]⟩

/-! ## `chopprefix`, `chopsuffix` -/

/-- `chopprefix(s, r)` and `chopsuffix(s, r)` return SubStrings of `s`; the result of
`chopsuffix` starts at the beginning of `s` (it is a prefix). -/
def ChopContract : Prop :=
  (∀ lib s re, chopprefixRe lib s re = do
    let (_, m) ← matchRe lib re s (firstindex s) ANCHORED
    match m with
    | none => liftR (RegexUnicode.Core.liftS (substring s (ix 1) (lastindex s)))
    | some m => liftR (RegexUnicode.Core.liftS (substring s (ncodeunits m.m.mat.view + ix 1) (lastindex s)))) ∧
  (∀ lib s re, chopsuffixRe lib s re = do
    let (_, m) ← matchRe lib re s (firstindex s) ENDANCHORED
    match m with
    | none => liftR (RegexUnicode.Core.liftS (substring s (ix 1) (lastindex s)))
    | some m =>
      if m.m.mat.ncu.val = 0 then liftR (RegexUnicode.Core.liftS (substring s (ix 1) (lastindex s)))
      else do
        let j ← liftR (RegexUnicode.Core.liftS (prevind s m.m.offset))
        liftR (RegexUnicode.Core.liftS (substring s (firstindex s) j)))

theorem chopContract : ChopContract := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-! ## Annotated matches, non-dense strings, `SubstitutionString`, replacement helpers -/

/-- A match in an `AnnotatedString` covers the same code units as the match in its
`String` (`_annotatedmatch`), with the `AnnotatedString` as parent;
`match(r, s)` starts at `firstindex(s)`; `match` and `findnext` on strings other
than dense UTF-8 strings throw `ArgumentError`; a `SubstitutionString` forwards
`ncodeunits`, `codeunit`, `isvalid` and `iterate` to its string and shows as
`s"..."`; `_write_capture` for a non-regex pattern accepts only group 0, writing the
matched SubString; `replace_err` throws; the iterator constructors convert the
string (keeping the annotations of an `AnnotatedString`); `eltype` is `RegexMatch`
and the size unknown. -/
def MiscContract : Prop :=
  (∀ m str, (annotatedMatch m str).1 = ⟨str, m.m.mat.offset, m.m.mat.ncu⟩ ∧
    (annotatedMatch m str).2 = m.m.captures.map (Option.map fun c => ⟨str, c.offset, c.ncu⟩)) ∧
  (∀ lib re str idx ao, matchAnnotated lib re str idx ao = (do
      let (_, m) ← matchRe lib re str.str idx ao
      pure (m.map (annotatedMatch · str)))) ∧
  (∀ lib re s, matchFirst lib re s = matchRe lib re s (ix 1)) ∧
  (∃ e, matchNonDense = .error e) ∧ (∃ e, findnextNonString = .error e) ∧
  (∀ s i, ssNcodeunits s = ncodeunits s.string ∧ ssCodeunit s i = codeunit s.string i ∧
    ssIsvalid s i = isvalidAt s.string i ∧ ssIterate s i = iterate s.string i ∧ ssCodeunitType s = 8) ∧
  (∀ esc s, showSubst esc s = "s\"".toUTF8.toList ++ esc s.string ++ "\"".toUTF8.toList ∧ (sStr s.string).string = s.string) ∧
  (∀ out group s r, group ≠ 0 → ∃ e, writeCaptureGeneric out group s r = .error e) ∧
  (∀ out s r sub, substring s r.1 r.2 = .ok sub →
    writeCaptureGeneric out 0 s r = .ok (ix sub.view.bytes.length, out ++ sub.view.bytes)) ∧
  (∀ (m : String), ∃ e, (replaceErr m : RJl Unit) = .error e) ∧
  (∀ re s ovr, (rmiCtor re s ovr).string = ⟨s, []⟩ ∧ (rmiCtor re s ovr).overlap = ovr) ∧
  (∀ re s ovr, (rmiCtorAnnotated re s ovr).string = s ∧ (rmiCtorAnnotated re s ovr).overlap = ovr) ∧
  (∀ lib itr itr', compileItr lib itr = .ok itr' → itr'.string = itr.string ∧ itr'.overlap = itr.overlap) ∧
  rmiEltype = "RegexMatch" ∧ rmiIteratorSize = "SizeUnknown" ∧
  (∀ c, wrapChar c = "\\Q".toUTF8.toList ++ charBytes c ++ "\\E".toUTF8.toList)

theorem miscContract : MiscContract := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl,
    ⟨_, rfl⟩, ⟨_, rfl⟩, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩,
    fun out group s r h => ?_, fun out s r sub h => ?_, fun _ => ⟨_, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ => ⟨rfl, rfl⟩, fun lib itr itr' h => ?_, rfl, rfl, fun _ => rfl⟩
  · unfold writeCaptureGeneric
    simp only [h, ne_eq, not_false_eq_true, bind, Except.bind, replaceErr, if_true]
    exact ⟨_, rfl⟩
  · unfold writeCaptureGeneric
    simp [RegexUnicode.Core.liftS, h, bind, Except.bind, pure, Except.pure, Except.mapError]
  · unfold compileItr at h
    cases hc : compileRegex lib itr.regex with
    | error e => rw [hc] at h; cases h
    | ok p => rw [hc] at h; cases h; exact ⟨rfl, rfl⟩

/-- `RegexAndMatchData(re)` allocates one match-data block, which
`_free_pat_replacer` frees; `findnext(::RegexAndMatchData, str, i)` and
`findnext(::Regex, str, i)` throw `BoundsError` for `i > nextind(str, lastindex(str))`. -/
def PatReplacerContract : Prop :=
  (∀ lib re, patReplacer lib re = regexAndMatchData lib re) ∧
  (∀ md, freePatReplacer md = freeMatchData md) ∧
  (∀ re c md s idx, findnextRMD re c md s idx = do
    let e1 ← liftR (RegexUnicode.Core.liftS (nextind s (lastindex s)))
    if idx.val > e1.val then throw (.str boundsErr)
    let matched ← exec c s (idx - ix 1) re.mopts md
    if matched then do
      let some v ← ovecPtr md | pure none
      let b ← liftR (RegexUnicode.Core.liftS (prevind s (ix (v.stop + 1))))
      pure (some (RegexUnicode.Core.mkRange (ix (v.start + 1)) b))
    else pure none) ∧
  (∀ lib re s idx, findnextRe lib re s idx = do
    let e1 ← liftR (RegexUnicode.Core.liftS (nextind s (lastindex s)))
    if idx.val > e1.val then throw (.str boundsErr)
    let opts := re.mopts
    let (re, c) ← liftR (compileRegex lib re)
    let (matched, data) ← execRData c s (idx - ix 1) opts
    let ans ← if matched then do
        let some v ← ovecPtr data | pure none
        let b ← liftR (RegexUnicode.Core.liftS (prevind s (ix (v.stop + 1))))
        pure (some (RegexUnicode.Core.mkRange (ix (v.start + 1)) b))
      else pure none
    freeMatchData data
    return (re, ans))

set_option maxRecDepth 10000 in
theorem patReplacerContract : PatReplacerContract := by
  exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

end JuliaLean.StringsCovB.Rx
