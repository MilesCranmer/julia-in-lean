import JuliaLean.DocsSyntaxCov.TomlLex

/-!
# Properties of the TOML lexer with comment capture, the comment containers, the parser
constructors and the error formatting (`base/toml/parser.jl`)
-/

namespace JuliaLean.DocsSyntaxCov.TomlLex

open JuliaLean JuliaLean.DocsSyntaxCov
open JuliaLean.Toml (Str ch EOF iterate slice rawOf iswhitespace isnewline ErrType)

/-! ## Character utilities -/

/-- `next_char` records the old position in `prevpos`, moves `pos` past the character
`iterate` reads, and counts lines and columns: a newline starts line `line + 1` at column `0`,
any other character (or the end, which returns `EOF_CHAR`) adds one column. -/
def NextCharSpec : Prop :=
  ∀ l : LP,
    (nextChar l).2.prevpos = l.pos ∧ (nextChar l).2.str = l.str ∧
    (nextChar l).2.currentChar = l.currentChar ∧ (nextChar l).2.comments = l.comments ∧
    (iterate l.str l.pos = none → (nextChar l).1 = EOF ∧ (nextChar l).2.pos = l.pos ∧
      (nextChar l).2.line = l.line ∧ (nextChar l).2.column = l.column + 1) ∧
    (∀ c p, iterate l.str l.pos = some (c, p) → (nextChar l).1 = c ∧ (nextChar l).2.pos = p ∧
      (c = ch '\n' → (nextChar l).2.line = l.line + 1 ∧ (nextChar l).2.column = 0) ∧
      (c ≠ ch '\n' → (nextChar l).2.line = l.line ∧ (nextChar l).2.column = l.column + 1))

theorem nextCharSpec : NextCharSpec := by
  intro l
  unfold nextChar
  cases h : iterate l.str l.pos with
  | none => simp
  | some cp =>
    obtain ⟨c, p⟩ := cp
    by_cases hc : c = ch '\n'
    · simp [hc]
    · have : (c == ch '\n') = false := by simpa using hc
      simp [this, hc]

/-- `eat_char` returns the look-ahead character and replaces it by the next one. -/
def EatCharSpec : Prop :=
  ∀ l : LP, (eatChar l).1 = l.currentChar ∧
    (eatChar l).2 = { (nextChar l).2 with currentChar := (nextChar l).1 }

theorem eatCharSpec : EatCharSpec := fun _ => ⟨rfl, rfl⟩

/-- `peek` is the look-ahead character. -/
def PeekSpec : Prop := ∀ l : LP, peek l = l.currentChar

theorem peekSpec : PeekSpec := fun _ => rfl

/-- `accept(l, f)` eats the look-ahead exactly when it is not `EOF_CHAR` and `f` takes it, and
otherwise leaves the parser unchanged. -/
def AcceptSpec : Prop :=
  ∀ (f : Acc) (l : LP), accept f l =
    if l.currentChar ≠ EOF ∧ f.test l.currentChar = true then (true, (eatChar l).2) else (false, l)

theorem accept_eq (f : Acc) (l : LP) : accept f l =
    if l.currentChar ≠ EOF ∧ f.test l.currentChar = true then (true, (eatChar l).2) else (false, l) := by
  unfold accept peek
  by_cases he : l.currentChar = EOF
  · simp [he]
  · have : (l.currentChar == EOF) = false := by simpa using he
    by_cases ht : f.test l.currentChar = true <;> simp [this, he, ht]

theorem acceptSpec : AcceptSpec := accept_eq

theorem accept_false (f : Acc) (l : LP) (h : (accept f l).1 = false) : (accept f l).2 = l := by
  rw [accept_eq] at h ⊢
  split <;> simp_all

/-- The fields that eating characters leaves alone. -/
def Keeps (l l' : LP) : Prop :=
  l'.str = l.str ∧ l'.comments = l.comments ∧ l'.pendingComments = l.pendingComments ∧
    l'.capturedComment = l.capturedComment ∧ l'.activeTablePath = l.activeTablePath ∧
    l'.inArrayTable = l.inArrayTable ∧ l'.lastItemPath = l.lastItemPath

theorem Keeps.refl (l : LP) : Keeps l l := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {a b c : LP} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩

theorem nextChar_keeps (l : LP) : Keeps l (nextChar l).2 := by
  unfold nextChar
  cases iterate l.str l.pos with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some cp =>
    obtain ⟨c, p⟩ := cp
    by_cases hc : (c == ch '\n') = true
    · simp only [hc, if_true]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [hc, Bool.false_eq_true, if_false]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem eatChar_keeps (l : LP) : Keeps l (eatChar l).2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := nextChar_keeps l
  exact ⟨a1, a2, a3, a4, a5, a6, a7⟩

theorem accept_keeps (f : Acc) (l : LP) : Keeps l (accept f l).2 := by
  rw [accept_eq]
  split
  · exact eatChar_keeps l
  · exact Keeps.refl l

theorem acceptBatch_keeps (f : Acc) : ∀ (fuel : Nat) (l : LP) (r : Bool) (l' : LP),
    acceptBatch f fuel l = .ok (r, l') → Keeps l l'
  | 0, _, _, _, h => by simp [acceptBatch] at h
  | n + 1, l, r, l', h => by
    unfold acceptBatch at h
    cases hb : (accept f l).1 with
    | false =>
      have h2 := accept_false f l hb
      simp only [hb, Bool.false_eq_true, if_false, exc_pure] at h
      cases h
      rw [h2]; exact Keeps.refl l
    | true =>
      simp only [hb, if_true] at h
      cases hr : acceptBatch f n (accept f l).2 with
      | error e => rw [hr] at h; cases h
      | ok p =>
        rw [hr] at h
        obtain ⟨_, l''⟩ := p
        simp only [exc_bind_ok, exc_pure] at h
        cases h
        exact (accept_keeps f l).trans (acceptBatch_keeps f n _ _ _ hr)

/-- `accept_batch(l, f)` eats a maximal run of accepted characters: it reports whether the
first was accepted, and afterwards the look-ahead is not accepted. -/
def AcceptBatchSpec : Prop :=
  ∀ (f : Acc) (fuel : Nat) (l : LP) (r : Bool) (l' : LP), acceptBatch f fuel l = .ok (r, l') →
    r = (accept f l).1 ∧ (accept f l').1 = false

theorem acceptBatch_spec (f : Acc) : ∀ (fuel : Nat) (l : LP) (r : Bool) (l' : LP),
    acceptBatch f fuel l = .ok (r, l') → r = (accept f l).1 ∧ (accept f l').1 = false
  | 0, _, _, _, h => by simp [acceptBatch] at h
  | n + 1, l, r, l', h => by
    unfold acceptBatch at h
    cases hb : (accept f l).1 with
    | false =>
      have h2 := accept_false f l hb
      simp only [hb, Bool.false_eq_true, if_false, exc_pure] at h
      cases h
      exact ⟨rfl, by rw [h2]; exact hb⟩
    | true =>
      simp only [hb, if_true] at h
      cases hr : acceptBatch f n (accept f l).2 with
      | error e => rw [hr] at h; cases h
      | ok p =>
        rw [hr] at h
        obtain ⟨_, l''⟩ := p
        simp only [exc_bind_ok, exc_pure] at h
        cases h
        exact ⟨rfl, (acceptBatch_spec f n _ _ _ hr).2⟩

theorem acceptBatchSpec : AcceptBatchSpec := acceptBatch_spec

/-- `accept_n(l, n, f)` returns immediately at zero and otherwise accepts one character,
stopping on failure or recurring for the remaining count. -/
def AcceptNSpec : Prop :=
  (∀ (f : Acc) (l : LP), acceptN f 0 l = (true, l)) ∧
  ∀ (f : Acc) (n : Nat) (l : LP), acceptN f (n + 1) l =
    let (ok, l) := accept f l
    if !ok then (false, l) else acceptN f n l

theorem acceptNSpec : AcceptNSpec := by
  exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- `iswhitespace` is space or tab, `isnewline` is `\n` or `\r`. -/
def WsNlSpec : Prop :=
  (∀ c, iswhitespace c = true ↔ c = ch ' ' ∨ c = ch '\t') ∧
  (∀ c, isnewline c = true ↔ c = ch '\n' ∨ c = ch '\r')

theorem wsNlSpec : WsNlSpec := ⟨fun c => by simp [iswhitespace], fun c => by simp [isnewline]⟩

/-- After `skip_ws` the look-ahead is not a space or tab; after `skip_ws_nl_no_comment` it is not
whitespace or a newline (or it is `EOF_CHAR`). -/
def SkipWsSpec : Prop :=
  (∀ fuel (l : LP) r l', skipWs fuel l = .ok (r, l') → l'.currentChar = EOF ∨ iswhitespace l'.currentChar = false) ∧
  (∀ fuel (l : LP) r l', skipWsNlNoComment fuel l = .ok (r, l') →
    l'.currentChar = EOF ∨ (iswhitespace l'.currentChar = false ∧ isnewline l'.currentChar = false))

theorem not_accepted (f : Acc) (l : LP) (h : (accept f l).1 = false) :
    l.currentChar = EOF ∨ f.test l.currentChar = false := by
  rw [accept_eq] at h
  by_cases he : l.currentChar = EOF
  · exact Or.inl he
  · right
    cases ht : f.test l.currentChar with
    | false => rfl
    | true => simp [he, ht] at h

theorem skipWsSpec : SkipWsSpec := by
  refine ⟨fun fuel l r l' h => ?_, fun fuel l r l' h => ?_⟩
  · exact not_accepted _ _ (acceptBatch_spec _ fuel l r l' h).2
  · rcases not_accepted _ _ (acceptBatch_spec _ fuel l r l' h).2 with h1 | h1
    · exact Or.inl h1
    · right; simpa [Acc.test] using h1

/-- `set_marker!` records `prevpos`; `take_substring` returns the bytes from the marker to just
before the look-ahead character. -/
def MarkerSpec : Prop :=
  (∀ l : LP, setMarker l = { l with marker := l.prevpos }) ∧
  (∀ l : LP, takeSubstring l = slice l.str l.marker (l.prevpos - 1))

theorem markerSpec : MarkerSpec := ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## Comment capture -/

/-- `skip_comment` skips a comment exactly when the look-ahead is `#`: it eats the rest of the
line up to (not including) the newline, and with comment capture records the text after `#`;
otherwise it leaves the parser unchanged. -/
def SkipCommentSpec : Prop :=
  ∀ fuel (l : LP) r l', skipComment fuel l = .ok (r, l') →
    r = (accept (.char (ch '#')) l).1 ∧
    (r = false → l' = l) ∧
    (r = true → (l'.currentChar = EOF ∨ isnewline l'.currentChar = true) ∧ l'.str = l.str ∧
      l'.comments = l.comments ∧ l'.pendingComments = l.pendingComments) ∧
    (r = true → l.comments.isSome → l'.capturedComment = slice l.str (eatChar l).2.prevpos (l'.prevpos - 1)) ∧
    (r = true → l.comments = none → l'.capturedComment = l.capturedComment)

theorem hash_accept (l : LP) (h : (accept (.char (ch '#')) l).1 = true) :
    (accept (.char (ch '#')) l).2 = (eatChar l).2 := by
  rw [accept_eq] at h ⊢; split <;> simp_all

theorem skipCommentSpec : SkipCommentSpec := by
  intro fuel l r l' h
  unfold skipComment at h
  cases hf : (accept (.char (ch '#')) l).1 with
  | false =>
    have h2 := accept_false _ l hf
    simp only [hf, Bool.false_eq_true, if_false, exc_pure] at h
    cases h
    exact ⟨rfl, fun _ => h2, by simp, by simp, by simp⟩
  | true =>
    have he := hash_accept l hf
    have hk := accept_keeps (.char (ch '#')) l
    simp only [hf, if_true] at h
    rw [he] at h hk
    cases hc : l.comments with
    | none =>
      have hc' : (eatChar l).2.comments = none := by rw [hk.2.1, hc]
      simp only [hc'] at h
      cases hr : acceptBatch (.fn fun c => !isnewline c) fuel (eatChar l).2 with
      | error e => rw [hr] at h; cases h
      | ok p =>
        rw [hr] at h
        obtain ⟨_, l''⟩ := p
        simp only [exc_bind_ok, exc_pure] at h
        cases h
        have hk2 := hk.trans (acceptBatch_keeps _ fuel _ _ _ hr)
        have hna := not_accepted _ _ (acceptBatch_spec _ fuel _ _ _ hr).2
        refine ⟨rfl, by simp, fun _ => ⟨?_, hk2.1, hk2.2.1.trans hc, hk2.2.2.1⟩,
          by simp [hc], fun _ _ => hk2.2.2.2.1⟩
        rcases hna with h1 | h1
        · exact Or.inl h1
        · right; simpa [Acc.test] using h1
    | some c =>
      have hc' : (eatChar l).2.comments = some c := by rw [hk.2.1, hc]
      simp only [hc'] at h
      cases hr : acceptBatch (.fn fun c => !isnewline c) fuel (eatChar l).2 with
      | error e => rw [hr] at h; cases h
      | ok p =>
        rw [hr] at h
        obtain ⟨_, l''⟩ := p
        simp only [exc_bind_ok, exc_pure] at h
        cases h
        have hk2 := hk.trans (acceptBatch_keeps _ fuel _ _ _ hr)
        have hk3 := acceptBatch_keeps _ fuel _ _ _ hr
        have hna := not_accepted _ _ (acceptBatch_spec _ fuel _ _ _ hr).2
        refine ⟨rfl, by simp, fun _ => ⟨?_, hk2.1, hk2.2.1.trans hc, hk2.2.2.1⟩,
          fun _ _ => ?_, fun _ h => by simp [hc] at h⟩
        · rcases hna with h1 | h1
          · exact Or.inl h1
          · right; simpa [Acc.test] using h1
        · simp only
          rw [hk3.1, hk.1]

/-- One iteration of `skip_ws_nl` consumes whitespace, then a comment, queues a captured
comment, and either stops or recurses. -/
def SkipWsNlSpec : Prop :=
  ∀ fuel k (l : LP), skipWsNl fuel (k + 1) l = do
    let (skippedWs, l) ← acceptBatch (.fn fun x => iswhitespace x || isnewline x) fuel l
    let (skippedComment, l) ← skipComment fuel l
    let l := if skippedComment && l.comments.isSome then
      { l with pendingComments := l.pendingComments ++ [l.capturedComment] } else l
    if !skippedWs && !skippedComment then return (false, l)
    let (_, l) ← skipWsNl fuel k l
    return (true, l)

theorem skipWsNlSpec : SkipWsNlSpec := by intro fuel k l; rfl

/-- `skip_ws_comment` skips spaces and then a comment if one starts there. -/
def SkipWsCommentSpec : Prop :=
  ∀ fuel (l : LP), skipWsComment fuel l = (do let (_, l) ← skipWs fuel l; skipComment fuel l)

theorem skipWsCommentSpec : SkipWsCommentSpec := fun _ _ => rfl

/-- `flush_pending_comments!` mirrors the queue move and final queue clear. -/
def FlushSpec : Prop :=
  ∀ l : LP, flushPendingComments l =
    if l.pendingComments.isEmpty then l
    else
      let l := match l.comments with
        | some c =>
          if !l.inArrayTable then
            let (fl, old) := dgetBang c.floating l.activeTablePath []
            { l with comments := some { c with
                floating := dset fl l.activeTablePath (old ++ l.pendingComments) } }
          else l
        | none => l
      { l with pendingComments := [] }

theorem dget_dset {κ α : Type} [BEq κ] [LawfulBEq κ] (d : Dict κ α) (k : κ) (v : α) :
    dget (dset d k v) k = some v := by
  unfold dget dset
  split
  · rename_i h
    induction d with
    | nil => simp at h
    | cons p ps ih =>
      by_cases hp : p.1 = k
      · simp [hp]
      · have hb : (p.1 == k) = false := by simpa using hp
        have h' : ps.any (·.1 == k) = true := by simpa [hb] using h
        simp only [List.map_cons, hb, Bool.false_eq_true, if_false, List.find?_cons]
        exact ih h'
  · rename_i h
    have : List.find? (fun p => p.1 == k) d = none := by
      rw [List.find?_eq_none]
      intro x hx hk
      exact h (List.any_eq_true.mpr ⟨x, hx, hk⟩)
    simp [List.find?_append, this]

theorem dgetBang_fst {κ α : Type} [BEq κ] [LawfulBEq κ] (d : Dict κ α) (k : κ) (dflt : α) :
    (dgetBang d k dflt).2 = (dget d k).getD dflt ∧
      dset (dgetBang d k dflt).1 k = fun v => dset (dgetBang d k dflt).1 k v := by
  unfold dgetBang
  cases dget d k <;> simp

theorem dget_dset_bang {κ α : Type} [BEq κ] [LawfulBEq κ] (d : Dict κ α) (k : κ) (dflt v : α) :
    dget (dset (dgetBang d k dflt).1 k v) k = some v := dget_dset _ _ _

theorem flushSpec : FlushSpec := fun _ => rfl

/-- `attach_pending_comments!(l, path)` appends the queued comments to the comments above `path`
and empties the queue (a `TypeError` without comment capture, nothing with an empty queue);
`attach_inline_comment!` records the captured comment as the inline comment of the last item,
keeping the comments above it, and does nothing without a last item. -/
def AttachSpec : Prop :=
  (∀ (l : LP) (path : List Str), l.pendingComments = [] → attachPendingComments path l = .ok l) ∧
  (∀ (l : LP) (path : List Str), l.pendingComments ≠ [] → l.comments = none →
    attachPendingComments path l = .error .typeError) ∧
  (∀ (l : LP) (path : List Str) (c : Comments) (l' : LP), l.comments = some c →
    l.pendingComments ≠ [] → attachPendingComments path l = .ok l' →
    l'.pendingComments = [] ∧
    (l'.comments.map fun c' => dget c'.items path) =
      some (some (let b := (dget c.items path).getD CommentBlock.new
        { b with above := b.above ++ l.pendingComments }))) ∧
  (∀ l : LP, l.lastItemPath = none → attachInlineComment l = .ok l) ∧
  (∀ (l : LP) (path : List Str), l.lastItemPath = some path → l.comments = none →
    attachInlineComment l = .error .typeError) ∧
  (∀ (l : LP) (path : List Str) (c : Comments) (l' : LP), l.lastItemPath = some path →
    l.comments = some c → attachInlineComment l = .ok l' →
    (l'.comments.map fun c' => dget c'.items path) =
      some (some { (dget c.items path).getD CommentBlock.new with inline := some l.capturedComment }))

theorem dgetBang_snd {κ α : Type} [BEq κ] (d : Dict κ α) (k : κ) (dflt : α) :
    (dgetBang d k dflt).2 = (dget d k).getD dflt := by
  unfold dgetBang; cases dget d k <;> rfl

theorem attachSpec : AttachSpec := by
  refine ⟨fun l path h => by simp [attachPendingComments, h], fun l path hp hc => ?_,
    fun l path c l' hc hp h => ?_, fun l h => by simp [attachInlineComment, h],
    fun l path h1 h2 => by simp [attachInlineComment, h1, h2], fun l path c l' h1 h2 h => ?_⟩
  · have hne : l.pendingComments.isEmpty = false := by simpa using hp
    simp [attachPendingComments, hne, hc]
  · have hne : l.pendingComments.isEmpty = false := by simpa using hp
    simp only [attachPendingComments, hne, Bool.false_eq_true, if_false, hc, exc_pure] at h
    cases h
    refine ⟨rfl, ?_⟩
    simp only [Option.map_some, dget_dset, dgetBang_snd]
  · simp only [attachInlineComment, h1, h2, exc_pure] at h
    cases h
    simp only [Option.map_some, dget_dset, dgetBang_snd]

/-- `skip_ws_nl_toplevel` is `skip_ws_nl` without comment capture; with it, it stops at a
look-ahead that is not whitespace, a newline or `#`, and every comment it skips is queued or
(after a blank line) flushed. -/
def ToplevelSpec : Prop :=
  (∀ fuel (l : LP), l.comments = none → skipWsNlToplevel fuel l = skipWsNl fuel fuel l) ∧
  (∀ fuel (l : LP), l.comments.isSome → skipWsNlToplevel fuel l = toplevelLoop fuel fuel 0 l) ∧
  (∀ k progress nlines (l : LP) r n' l', toplevelWs k progress nlines l = .ok (r, n', l') →
    l'.currentChar = EOF ∨ (iswhitespace l'.currentChar = false ∧ isnewline l'.currentChar = false))

theorem toplevelWs_stop : ∀ k progress nlines (l : LP) r n' l', toplevelWs k progress nlines l = .ok (r, n', l') →
    l'.currentChar = EOF ∨ (iswhitespace l'.currentChar = false ∧ isnewline l'.currentChar = false)
  | 0, _, _, _, _, _, _, h => by simp [toplevelWs] at h
  | k + 1, progress, nlines, l, r, n', l', h => by
    unfold toplevelWs at h
    by_cases hw : iswhitespace (peek l) = true
    · simp only [hw, if_true] at h
      exact toplevelWs_stop k _ _ _ _ _ _ h
    · simp only [hw, Bool.false_eq_true, if_false] at h
      by_cases hn : isnewline (peek l) = true
      · simp only [hn, if_true] at h
        exact toplevelWs_stop k _ _ _ _ _ _ h
      · simp only [hn, Bool.false_eq_true, if_false, exc_pure] at h
        cases h
        right
        exact ⟨by simpa [peek] using hw, by simpa [peek] using hn⟩

theorem toplevelSpec : ToplevelSpec := by
  refine ⟨fun fuel l h => by simp [skipWsNlToplevel, h], fun fuel l h => ?_, toplevelWs_stop⟩
  have : l.comments.isNone = false := by cases hc : l.comments <;> simp_all
  simp [skipWsNlToplevel, this]

/-- `path_traverses_array(l, keys)` walks `keys` down from the root: it is `true` as soon as a
key holds an array, continues through tables, and is `false` at a missing key, a value that is
no table, or the end of the keys. -/
def PathTraversesArraySpec : Prop :=
  ∀ (d : List (Str × TV)) (ks : List Str),
    pathTraversesArray d ks = true ↔
      ∃ pre k rest xs kvs, ks = pre ++ k :: rest ∧ walkDicts d pre = some kvs ∧
        (kvs.find? (·.1 == k)).map (·.2) = some (TV.vec xs)
where
  walkDicts : List (Str × TV) → List Str → Option (List (Str × TV))
    | d, [] => some d
    | d, k :: ks => match (d.find? (·.1 == k)).map (·.2) with
      | some (TV.dict kvs) => walkDicts kvs ks
      | _ => none

theorem pathTraversesArraySpec : PathTraversesArraySpec := by
  intro d ks
  induction ks generalizing d with
  | nil =>
    simp only [pathTraversesArray, Bool.false_eq_true, false_iff]
    rintro ⟨pre, k, rest, xs, kvs, h, -⟩
    cases pre <;> simp at h
  | cons k ks ih =>
    unfold pathTraversesArray
    constructor
    · intro h
      split at h
      · rename_i xs hx
        exact ⟨[], k, ks, xs, d, rfl, rfl, hx⟩
      · rename_i kvs hx
        obtain ⟨pre, k', rest, xs, kvs', h1, h2, h3⟩ := (ih kvs).mp h
        refine ⟨k :: pre, k', rest, xs, kvs', by simp [h1], ?_, h3⟩
        simp only [PathTraversesArraySpec.walkDicts, hx]; exact h2
      · simp at h
    · rintro ⟨pre, k', rest, xs, kvs, h1, h2, h3⟩
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [PathTraversesArraySpec.walkDicts, Option.some.injEq] at h2
        subst h2
        simp [h3]
      | cons p pre =>
        simp only [List.cons_append, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [PathTraversesArraySpec.walkDicts] at h2
        split at h2
        · rename_i kvs' hx
          rw [hx]
          exact (ih kvs').mpr ⟨pre, k', rest, xs, kvs, rfl, h2, h3⟩
        · cases h2

/-! ## Comment containers -/

/-- `CommentBlock()` is empty; `Comments()` and `empty!(c)` are empty and `isempty` holds exactly
for comments without items or floating comments; `==` on blocks is equality of both fields; `==`
on comments is reflexive (for dictionaries, whose keys are distinct). -/
def CommentContainers : Prop :=
  CommentBlock.new = ⟨[], none⟩ ∧ Comments.new = ⟨[], []⟩ ∧
  (∀ c : Comments, c.empty = Comments.new) ∧
  (∀ c : Comments, c.isempty = true ↔ c.items = [] ∧ c.floating = []) ∧
  (∀ a b : CommentBlock, CommentBlock.eq a b = true ↔ a = b) ∧
  (∀ c : Comments, (c.items.map (·.1)).Nodup → (c.floating.map (·.1)).Nodup → Comments.eq c c = true)

theorem dget_of_mem {κ α : Type} [BEq κ] [LawfulBEq κ] :
    ∀ (d : Dict κ α) (k : κ) (v : α), (d.map (·.1)).Nodup → (k, v) ∈ d → dget d k = some v
  | [], _, _, _, h => by simp at h
  | (k', v') :: rest, k, v, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at h
    rcases h with h | h
    · cases h; simp [dget]
    · have hk : k' ≠ k := by
        intro he; subst he
        exact hn.1 (List.mem_map.mpr ⟨(k', v), h, rfl⟩)
      have := dget_of_mem rest k v hn.2 h
      unfold dget at this ⊢
      simp [hk, this]

theorem dictEq_refl {κ α : Type} [BEq κ] [LawfulBEq κ] (eqv : α → α → Bool) (hr : ∀ a, eqv a a = true)
    (d : Dict κ α) (hn : (d.map (·.1)).Nodup) : dictEq eqv d d = true := by
  unfold dictEq
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro p hp
  obtain ⟨k, v⟩ := p
  simp [dget_of_mem d k v hn hp, hr]

theorem commentContainers : CommentContainers := by
  refine ⟨rfl, rfl, fun _ => rfl, fun c => by simp [Comments.isempty], fun a b => ?_, fun c h1 h2 => ?_⟩
  · obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
    simp [CommentBlock.eq]
  · unfold Comments.eq
    rw [dictEq_refl _ (fun a => by obtain ⟨a1, a2⟩ := a; simp [CommentBlock.eq]) _ h1,
      dictEq_refl _ (fun a => by simp) _ h2]
    rfl

/-! ## Construction -/

/-- `Parser{Dates}(str; ...)` holds the first character of `str` as the look-ahead and the
emptied `comments` (the first `eat_char` of `startup` returns the initial `EOF_CHAR`, so the
BOM test never fires); `Parser{Dates}()` parses `""`, `Parser{Dates}(io)` the bytes read, and
`reinit!(p, str; ...)` gives exactly the state of a fresh parser of `str` whatever `p` held. -/
def ParserConstruction : Prop :=
  (∀ (str : Str) (fp : Option Str) (c : Option Comments),
    parserNew str fp c = (eatChar (freshState str fp c)).2 ∧
    (parserNew str fp c).comments = c.map Comments.empty) ∧
  parserEmpty = parserNew [] ∧ (∀ b, parserIO b = parserNew b) ∧
  (∀ (p : LP) (str : Str) (fp : Option Str) (c : Option Comments), reinit p str fp c = parserNew str fp c)

theorem parserConstruction : ParserConstruction := by
  refine ⟨fun str fp c => ⟨?_, ?_⟩, rfl, fun _ => rfl, fun _ _ _ _ => rfl⟩
  · have : (EOF == rawOf 0xFEFF) = false := by decide
    simp [parserNew, startup, eatChar, freshState, this]
  · have : (EOF == rawOf 0xFEFF) = false := by decide
    have hk := (eatChar_keeps (freshState str fp c)).2.1
    simp only [parserNew, startup, this, Bool.false_eq_true, if_false]
    exact hk

/-! ## `@try` -/

/-- `@try expr` binds `expr` to `v`, returns `v` from the enclosing function when it is a
`ParserError`, and otherwise evaluates to `v`. -/
def TryMacro : Prop :=
  (∀ e, tryMacro e = .expr "block" [.expr "=" [.sym "v", esc e],
    .expr "&&" [call (.sym "isa") [.sym "v", .sym "ParserError"], .expr "return" [.sym "v"]], .sym "v"]) ∧
  (∀ {α β : Type} (e : ErrType) (k : α → Except ErrType β), tryValue (.error e) k = .error e) ∧
  (∀ {α β : Type} (x : α) (k : α → Except ErrType β), tryValue (.ok x) k = k x)

theorem tryMacroSpec : TryMacro := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## Errors -/

/-- `ParserError(type, data)` and `ParserError(type)` leave the location fields unset. -/
def ParserErrorCtors : Prop :=
  (∀ t, ParserError.mk1 t = ⟨t, none, none, none, none, none, none, false⟩) ∧
  (∀ t d, ParserError.mk2 t d = ⟨t, d, none, none, none, none, none, false⟩)

theorem parserErrorCtors : ParserErrorCtors := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Every error type has a non-empty message (the `@assert` loop, lines 321-323); the message
for an invalid bare key character appends the escaped character (a `TypeError` without one);
other types print their message alone. -/
def FormatErrorSpec : Prop :=
  (∀ t : ErrType, errMessage t ≠ "") ∧
  (∀ (esc : Nat → Str) (e : ParserError), e.type = .ErrInvalidBareKeyCharacter →
    ∀ c, e.data = some c → formatErrorMessage esc e =
      .ok ((errMessage e.type).toUTF8.toList.map (·.toNat) ++ [58, 32, 39] ++ esc c ++ [39])) ∧
  (∀ (esc : Nat → Str) (e : ParserError), e.type = .ErrInvalidBareKeyCharacter → e.data = none →
    formatErrorMessage esc e = .error .typeError) ∧
  (∀ (esc : Nat → Str) (e : ParserError), e.type ≠ .ErrInvalidBareKeyCharacter →
    formatErrorMessage esc e = .ok ((errMessage e.type).toUTF8.toList.map (·.toNat)))

theorem formatErrorSpec : FormatErrorSpec := by
  refine ⟨fun t => ?_, fun esc e ht c hd => ?_, fun esc e ht hd => ?_, fun esc e ht => ?_⟩
  · cases t <;> simp [errMessage]
  · simp [formatErrorMessage, ht, hd]
  · simp [formatErrorMessage, ht, hd]
  · have : (e.type == .ErrInvalidBareKeyCharacter) = false := by simpa using ht
    simp [formatErrorMessage, this]

/-- `point_to_line(str, a, b)` checks the interval, normalizes both indices, finds the start
of the line, and runs its character loop. -/
def PointToLineSpec : Prop :=
  (∀ caret s a b, ¬ b ≥ a → pointToLine caret s a b = .error .assertionError) ∧
  ∀ caret s a b a' b' p, b ≥ a → thisind s a = .ok a' → thisind s b = .ok b' →
    prevind s a' = .ok p → pointToLine caret s a b =
      pointToLine.go caret s a b (s.length + 2) ((findprevNewline s p).getD 0 + 1) [] []

theorem pointToLineSpec : PointToLineSpec := by
  refine ⟨fun caret s a b h => ?_, fun caret s a b a' b' p h h1 h2 h3 => ?_⟩
  · unfold pointToLine
    simp only [h, decide_false, Bool.not_false, if_true]
    change (Except.error DErr.assertionError >>= fun _ : Unit => _) = .error DErr.assertionError
    rfl
  · simp [pointToLine, h, h1, h2, h3]

/-- `showerror(io, err)` formats the header and location, then the message, source line and
marker line, with a `TypeError` when the position or source is absent. -/
def ShowerrorSpec : Prop :=
  ∀ (st : Style) (showInt : Int → Str) (esc : Nat → Str) (err : ParserError),
    showerror st showInt esc err = do
      let head := st.error (bytes% "TOML Parser error:\n")
      let f := err.filepath.getD (bytes% "none")
      let loc := st.bold (f ++ [58] ++ showOptInt showInt err.line ++ [58] ++
        showOptInt showInt err.column)
      let msg ← formatErrorMessage esc err
      let pos ← match err.pos with
        | some p => pure p
        | none => throw .typeError
      let pos := if err.type == .ErrUnexpectedEofExpectedValue then pos + 1 else pos
      let s ← match err.str with
        | some s => pure s
        | none => throw .typeError
      let (str1, err1) ← pointToLine st.caret s pos pos
      pure (head ++ loc ++ st.error (bytes% " error: ") ++ msg ++ [10] ++ [32, 32] ++ str1 ++
        [10] ++ [32, 32] ++ err1)

theorem showerrorSpec : ShowerrorSpec := by
  intro st showInt esc err
  rfl

/-- `DateTime(y, m, d, h, mi, s, ms)` is `DateTime(Date(y, m, d), Time(h, mi, s, ms))`. -/
def DateTimeCtor : Prop :=
  ∀ y m d h mi s ms, dateTime7 y m d h mi s ms = ⟨⟨y, m, d⟩, ⟨h, mi, s, ms⟩⟩

theorem dateTimeCtor : DateTimeCtor := fun _ _ _ _ _ _ _ => rfl

/-- `copyto_typed!(a, b)` copies `b` into the front of `a`, keeping `a`'s length; it throws a
`TypeError` when an element of `b` is not of the element type. -/
def CopytoTypedSpec : Prop :=
  ∀ {α : Type} (isT : α → Bool) (a b : List α),
    (∀ r, copytoTyped isT a b = .ok r → r.length = a.length ∧ ∀ j < b.length, r[j]? = b[j]?) ∧
    ((∀ x ∈ b, isT x = true) → b.length ≤ a.length → ∃ r, copytoTyped isT a b = .ok r) ∧
    (b.any (fun x => !isT x) = true → ∃ e, copytoTyped isT a b = .error e)

theorem copyto_go {α : Type} (isT : α → Bool) : ∀ (b : List α) (i : Nat) (a r : List α),
    copytoTyped.go isT i a b = .ok r →
    r.length = a.length ∧ (∀ j < b.length, r[i + j]? = b[j]?) ∧ ∀ j < i, r[j]? = a[j]?
  | [], i, a, r, h => by
    simp only [copytoTyped.go, exc_pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, by simp, fun _ _ => rfl⟩
  | x :: xs, i, a, r, h => by
    unfold copytoTyped.go at h
    by_cases hx : isT x = true
    · simp only [hx, Bool.not_true, Bool.false_eq_true, if_false] at h
      by_cases hi : i < a.length
      · simp only [hi, if_true] at h
        obtain ⟨h1, h2, h3⟩ := copyto_go isT xs (i + 1) _ r h
        refine ⟨by simp [h1], fun j hj => ?_, fun j hj => ?_⟩
        · cases j with
          | zero =>
            rw [Nat.add_zero, h3 i (by omega)]
            simp [List.getElem?_set, hi]
          | succ j =>
            have := h2 j (by simp at hj; omega)
            rw [show i + (j + 1) = i + 1 + j by omega, this]
            simp
        · rw [h3 j (by omega)]
          simp [List.getElem?_set, show i ≠ j by omega]
      · simp [hi] at h
    · simp [hx] at h

theorem copytoTypedSpec : CopytoTypedSpec := by
  intro α isT a b
  refine ⟨fun r h => ?_, fun hall hlen => ?_, fun hany => ?_⟩
  · obtain ⟨h1, h2, -⟩ := copyto_go isT b 0 a r h
    exact ⟨h1, fun j hj => by simpa using h2 j hj⟩
  · have : ∀ (b : List α) (i : Nat) (a : List α), (∀ x ∈ b, isT x = true) → i + b.length ≤ a.length →
        ∃ r, copytoTyped.go isT i a b = .ok r := by
      intro b
      induction b with
      | nil => intro i a _ _; exact ⟨a, rfl⟩
      | cons x xs ih =>
        intro i a hall hlen
        have hx : isT x = true := hall x (by simp)
        have hi : i < a.length := by simp at hlen; omega
        unfold copytoTyped.go
        simp only [hx, Bool.not_true, Bool.false_eq_true, if_false, hi, if_true]
        exact ih (i + 1) _ (fun y hy => hall y (by simp [hy])) (by simp at hlen ⊢; omega)
    exact this b 0 a hall (by omega)
  · have : ∀ (b : List α) (i : Nat) (a : List α), b.any (fun x => !isT x) = true →
        ∃ e, copytoTyped.go isT i a b = .error e := by
      intro b
      induction b with
      | nil => intro i a h; simp at h
      | cons x xs ih =>
        intro i a h
        unfold copytoTyped.go
        by_cases hx : isT x = true
        · have h' : xs.any (fun x => !isT x) = true := by simpa [hx] using h
          simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
          split
          · exact ih _ _ h'
          · exact ⟨_, rfl⟩
        · simp [hx]
    exact this b 0 a hany

end JuliaLean.DocsSyntaxCov.TomlLex
