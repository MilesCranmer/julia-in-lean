import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.base.expr
import JuliaLean.base.io
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.string
import JuliaLean.base.toml.parser
import JuliaLean.Registry.Types


section

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

end

section

/-! Row-specific properties not supplied by the initial area models. -/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

namespace Parse

open JuliaLean.ParsePrint.IntParse

end Parse

namespace TomlPrint

end TomlPrint

namespace Binary

open JuliaLean.Platforms

end Binary

namespace TomlRows

open JuliaLean.Toml

def Runs {A : Type} (m : M A) (p : Parser) : Prop := ∃ r, m.run p = r

theorem runs {A : Type} (m : M A) (p : Parser) : Runs m p := by
  unfold Runs
  cases h : m.run p with
  | ok r => exact ⟨.ok r, rfl⟩
  | error e => exact ⟨.error e, rfl⟩

def ValueMethodTotality : Prop := ∀ (p : Parser) (lf fuel : Nat) (sgn : Int) (b : Bool)
    (f : Nat → Bool) (sx : IntSyntax),
  Runs (parse_toplevel lf fuel) p ∧
  Runs (parse_key fuel) p ∧
  Runs (parse_value lf fuel) p ∧
  Runs (parse_inline_table lf fuel) p ∧
  Runs (parse_inf sgn) p ∧
  Runs parse_nan p ∧
  Runs (parse_bool b) p ∧
  Runs (accept_batch_underscore fuel f) p ∧
  Runs (take_string_or_substring b) p ∧
  Runs (parse_intlike sx b) p ∧
  isvalid_hex p.current_char =
    (isdigit p.current_char || (ch 'a' ≤ p.current_char && p.current_char ≤ ch 'f') ||
      (ch 'A' ≤ p.current_char && p.current_char ≤ ch 'F')) ∧
  isvalid_oct p.current_char = (ch '0' ≤ p.current_char && p.current_char ≤ ch '7') ∧
  isvalid_binary p.current_char = (ch '0' ≤ p.current_char && p.current_char ≤ ch '1') ∧
  ok_end_value p.current_char =
    (iswhitespace p.current_char || p.current_char == ch '#' || p.current_char == EOF ||
      p.current_char == ch ']' || p.current_char == ch '}' || p.current_char == ch ',' ||
      p.current_char == ch '\n' || p.current_char == ch '\r')

theorem valueMethodTotality : ValueMethodTotality := by
  intro p lf fuel sgn b f sx
  exact ⟨runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _,
    runs _ _, runs _ _, rfl, rfl, rfl, rfl⟩

def DateMethodTotality : Prop := ∀ (p : Parser) (fuel : Nat) (f : Nat → Bool)
    (y m d h mi s ms : Int),
  Runs (accept_two f) p ∧
  Runs (try_return_datetime y m d h mi s ms) p ∧
  Runs (try_return_date y m d) p ∧
  Runs (try_return_time h mi s ms) p ∧
  Runs (_parse_local_time fuel false) p ∧
  Runs (parse_local_time fuel) p ∧
  Runs (parse_datetime fuel) p

theorem dateMethodTotality : DateMethodTotality := by
  intro p fuel f y m d h mi s ms
  exact ⟨runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _⟩

def StringMethodTotality : Prop := ∀ (p : Parser) (fuel : Nat) (quoted allow multiline : Bool),
  Runs (parse_string_start fuel quoted allow) p ∧
  Runs (parse_string_continue fuel multiline quoted) p ∧
  Runs (take_chunks quoted) p ∧
  (∀ x, stopCandidates true false x =
    (x != ch '"' && x != ch '\\' && (true || x != ch '\n'))) ∧
  (∀ x, stopCandidates false false x =
    (x != ch '"' && x != ch '\\' && (false || x != ch '\n'))) ∧
  (∀ x, stopCandidates true true x =
    (x != ch '\'' && x != ch '\\' && (true || x != ch '\n'))) ∧
  ∀ x, stopCandidates false true x =
    (x != ch '\'' && x != ch '\\' && (false || x != ch '\n'))

theorem stringMethodTotality : StringMethodTotality := by
  intro p fuel quoted allow multiline
  exact ⟨runs _ _, runs _ _, runs _ _, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end TomlRows

namespace Binary

open JuliaLean.Platforms

end Binary

namespace Syntax

end Syntax

end JuliaLean.DocsSyntaxCov

end


namespace JuliaLean.Proofs.base.toml.parser

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.toml.parser

namespace Round1

set_option linter.unusedVariables false

/-- Public `tryparse` reports invalid initial bare-key characters as `ParserError`
(`stdlib/TOML/docs/src/index.md:42-44`; TOML 1.0 `Keys`, raw spec lines 102-109;
`base/toml/parser.jl:599-616`). -/
def TryparseInvalidInitialBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (c : Char) (suffix : String)
    (p : Parser X D CI CF),
    isvalid_barekey_char (jc c) = false →
    c ≠ '"' → c ≠ '\'' → c ≠ '=' → c ≠ '[' → c ≠ '#' → c ≠ '\ufeff' →
    iswhitespace (jc c) = false → isnewline (jc c) = false →
    Parser_new o (lit (String.singleton c ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ after err,
      runP o (tryparse o) p = some (.ok (.error err, after)) ∧
      err.type = .ErrInvalidBareKeyCharacter

/-- Public `parse` throws a `ParserError` for an invalid initial bare-key character
(`stdlib/TOML/src/TOML.jl:116-120`; TOML 1.0 `Keys`, raw spec lines 102-109;
`base/toml/parser.jl:593-597`). -/
def ParseInvalidInitialBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (c : Char) (suffix : String)
    (p : Parser X D CI CF),
    isvalid_barekey_char (jc c) = false →
    c ≠ '"' → c ≠ '\'' → c ≠ '=' → c ≠ '[' → c ≠ '#' → c ≠ '\ufeff' →
    iswhitespace (jc c) = false → isnewline (jc c) = false →
    Parser_new o (lit (String.singleton c ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ err,
      runP o (parse o) p = some (.error (.parserError err)) ∧
      err.type = .ErrInvalidBareKeyCharacter

end Round1
namespace Round2

set_option linter.unusedVariables false

/-- TOML 1.0 keyless documents may contain spaces, tabs, LF, or CRLF only
(TOML 1.0 `Spec`, raw lines 45-46). -/
def tomlWhitespaceOnly : List Char → Prop
  | [] => True
  | '\r' :: '\n' :: rest => tomlWhitespaceOnly rest
  | c :: rest => (c = ' ' ∨ c = '\t' ∨ c = '\n') ∧ tomlWhitespaceOnly rest

/-- A public `tryparse` call reports a `ParserError` for an empty bare key
(`TOML.tryparse` docs, `stdlib/TOML/docs/src/index.md:42-44`; TOML 1.0 `Keys`, raw lines 130-136;
`base/toml/parser.jl:599-616`). -/
def TryparseEmptyBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (suffix : String)
    (p : Parser X D CI CF),
    Parser_new o (lit ("=" ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ after err,
      runP o (tryparse o) p = some (.ok (.error err, after))

/-- A public `parse` call throws `ParserError` for an empty bare key
(`TOML.parse` docs, `stdlib/TOML/src/TOML.jl:116-120`; TOML 1.0 `Keys`, raw lines 130-136;
`base/toml/parser.jl:593-597`). -/
def ParseEmptyBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (suffix : String)
    (p : Parser X D CI CF),
    Parser_new o (lit ("=" ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ err, runP o (parse o) p = some (.error (.parserError err))

/-- For an invalid initial bare key, `tryparse` reports the original input and the documented
line/column of the offending character (`stdlib/TOML/docs/src/index.md:42-61`; TOML 1.0 `Keys`,
raw lines 107-109; `base/toml/parser.jl:599-616`). -/
def TryparseInvalidInitialBareKeyLocation : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (suffix : String)
    (p : Parser X D CI CF),
    let input := String.singleton '@' ++ suffix
    Parser_new o (lit input) = some (.ok (.ok (), p)) →
    ∃ after err,
      runP o (tryparse o) p = some (.ok (.error err, after)) ∧
      err.str = some (lit input) ∧
      err.line = some (i64 1) ∧
      err.column = some (i64 1)

/-- The thrown `ParserError` for an invalid initial bare key reports the original input and
its offending line/column (`stdlib/TOML/src/TOML.jl:116-120`; TOML 1.0 `Keys`, raw lines 107-109;
`base/toml/parser.jl:593-616`). -/
def ParseInvalidInitialBareKeyLocation : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (suffix : String)
    (p : Parser X D CI CF),
    let input := String.singleton '@' ++ suffix
    Parser_new o (lit input) = some (.ok (.ok (), p)) →
    ∃ err,
      runP o (parse o) p = some (.error (.parserError err)) ∧
      err.str = some (lit input) ∧
      err.line = some (i64 1) ∧
      err.column = some (i64 1)

/-- Every valid whitespace-only TOML document returns the root table
(`TOML.tryparse` docs, `stdlib/TOML/docs/src/index.md:42-44`; TOML 1.0 `Spec`, raw lines 45-46,
and `Table`, raw lines 746-748; `base/toml/parser.jl:599-616`). -/
def TryparseWhitespaceOnlyReturnsRoot : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (text : String) (p : Parser X D CI CF),
    tomlWhitespaceOnly text.toList →
    Parser_new o (lit text) = some (.ok (.ok (), p)) →
    ∃ after root,
      runP o (tryparse o) p = some (.ok (.ok root, after)) ∧
      root = after.root

/-- `parse` returns the root table for every valid whitespace-only TOML document
(`TOML.parse` docs, `stdlib/TOML/src/TOML.jl:116-132`; TOML 1.0 `Spec`, raw lines 45-46,
and `Table`, raw lines 746-748; `base/toml/parser.jl:593-597`). -/
def ParseWhitespaceOnlyReturnsRoot : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (text : String) (p : Parser X D CI CF),
    tomlWhitespaceOnly text.toList →
    Parser_new o (lit text) = some (.ok (.ok (), p)) →
    ∃ after root,
      runP o (parse o) p = some (.ok (.ok root, after)) ∧
      root = after.root

end Round2
namespace Round5

set_option linter.unusedVariables false

/-- An unrecognized non-newline escape in a basic quoted key returns `ParserError`. LF/CR
continuations remain in the existing bug repro and are excluded here (`TOML.tryparse` docs,
`stdlib/TOML/docs/src/index.md:42-44`; TOML 1.1 `String`,
`toml-lang/toml/1.1.0/toml.md:250-355`; `base/toml/parser.jl:1383-1446`). The UTF-8 input-byte
bound keeps the input within Julia's `Int` string-index range. -/
def TryparseInvalidNonnewlineEscapeInQuotedKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (c : Char) (suffix : String)
    (p : Parser X D CI CF),
    c ≠ 'b' → c ≠ 't' → c ≠ 'n' → c ≠ 'f' → c ≠ 'r' → c ≠ 'e' →
    c ≠ '"' → c ≠ '\\' → c ≠ 'x' → c ≠ 'u' → c ≠ 'U' →
    c ≠ '\n' → c ≠ '\r' →
    let input := String.singleton '"' ++ String.singleton '\\' ++ String.singleton c ++ suffix
    input.utf8ByteSize < 2 ^ 62 →
    Parser_new o (lit input) = some (.ok (.ok (), p)) →
    ∃ after err,
      runP o (tryparse o) p = some (.ok (.error err, after))

/-- Public `parse` throws `ParserError` for an unrecognized non-newline escape in a basic quoted
key. LF/CR continuations remain in the existing bug repro and are excluded here (`TOML.parse` docs,
`stdlib/TOML/src/TOML.jl:116-120`; TOML 1.1 `String`,
`toml-lang/toml/1.1.0/toml.md:250-355`; `base/toml/parser.jl:1383-1446`). The UTF-8 input-byte
bound keeps the input within Julia's `Int` string-index range. -/
def ParseInvalidNonnewlineEscapeInQuotedKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (c : Char) (suffix : String)
    (p : Parser X D CI CF),
    c ≠ 'b' → c ≠ 't' → c ≠ 'n' → c ≠ 'f' → c ≠ 'r' → c ≠ 'e' →
    c ≠ '"' → c ≠ '\\' → c ≠ 'x' → c ≠ 'u' → c ≠ 'U' →
    c ≠ '\n' → c ≠ '\r' →
    let input := String.singleton '"' ++ String.singleton '\\' ++ String.singleton c ++ suffix
    input.utf8ByteSize < 2 ^ 62 →
    Parser_new o (lit input) = some (.ok (.ok (), p)) →
    ∃ err,
      runP o (parse o) p = some (.error (.parserError err))

end Round5



namespace Round4

open _root_.JuliaLean.base.toml.parser

set_option linter.unusedVariables false

/-- Public `tryparse` reports invalid initial bare-key characters as `ParserError`
(`stdlib/TOML/docs/src/index.md:42-44`; TOML 1.0 `Keys`, raw spec lines 102-109;
`base/toml/parser.jl:599-616`). The UTF-8 input-byte bound keeps the quantified input
realizable with Julia's `Int`-sized string indices. -/
def TryparseInvalidInitialBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (c : Char) (suffix : String)
    (p : Parser X D CI CF),
    isvalid_barekey_char (jc c) = false →
    c ≠ '"' → c ≠ '\'' → c ≠ '=' → c ≠ '[' → c ≠ '#' → c ≠ '\ufeff' →
    iswhitespace (jc c) = false → isnewline (jc c) = false →
    (String.singleton c ++ suffix).utf8ByteSize < 2^62 →
    Parser_new o (lit (String.singleton c ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ after err,
      runP o (tryparse o) p = some (.ok (.error err, after)) ∧
      err.type = .ErrInvalidBareKeyCharacter

/-- Public `parse` throws `ParserError` for an invalid initial bare-key character
(`stdlib/TOML/src/TOML.jl:116-120`; TOML 1.0 `Keys`, raw spec lines 102-109;
`base/toml/parser.jl:593-597`). The UTF-8 input-byte bound keeps the quantified input
realizable with Julia's `Int`-sized string indices. -/
def ParseInvalidInitialBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (c : Char) (suffix : String)
    (p : Parser X D CI CF),
    isvalid_barekey_char (jc c) = false →
    c ≠ '"' → c ≠ '\'' → c ≠ '=' → c ≠ '[' → c ≠ '#' → c ≠ '\ufeff' →
    iswhitespace (jc c) = false → isnewline (jc c) = false →
    (String.singleton c ++ suffix).utf8ByteSize < 2^62 →
    Parser_new o (lit (String.singleton c ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ err,
      runP o (parse o) p = some (.error (.parserError err)) ∧
      err.type = .ErrInvalidBareKeyCharacter

/-- A public `tryparse` call reports `ParserError` for an empty bare key
(`TOML.tryparse` docs, `stdlib/TOML/docs/src/index.md:42-44`; TOML 1.0 `Keys`,
raw lines 130-136; `base/toml/parser.jl:599-616`). The UTF-8 input-byte bound keeps the
quantified input realizable with Julia's `Int`-sized string indices. -/
def TryparseEmptyBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (suffix : String)
    (p : Parser X D CI CF),
    ("=" ++ suffix).utf8ByteSize < 2^62 →
    Parser_new o (lit ("=" ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ after err,
      runP o (tryparse o) p = some (.ok (.error err, after))

/-- A public `parse` call throws `ParserError` for an empty bare key
(`TOML.parse` docs, `stdlib/TOML/src/TOML.jl:116-120`; TOML 1.0 `Keys`,
raw lines 130-136; `base/toml/parser.jl:593-597`). The UTF-8 input-byte bound keeps the
quantified input realizable with Julia's `Int`-sized string indices. -/
def ParseEmptyBareKey : Prop :=
  ∀ {X Y E D CI CF} (o : Ops X Y E D CI CF) (suffix : String)
    (p : Parser X D CI CF),
    ("=" ++ suffix).utf8ByteSize < 2^62 →
    Parser_new o (lit ("=" ++ suffix)) = some (.ok (.ok (), p)) →
    ∃ err, runP o (parse o) p = some (.error (.parserError err))

end Round4

/-! ## ParserMonad -/

namespace JuliaLean.ChatGPT.Batch2.Group1

open JuliaLean JuliaLean.base.toml.parser
open JuliaLean.Proofs.base.toml.parser

section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)

 theorem el_pure_run {α : Type} (a : α) (p : Parser X D CI CF) :
    runP o (pure a) p = some (.ok (.ok a, p)) := rfl

 theorem el_throwP_run {α : Type} (err : ParserError) (p : Parser X D CI CF) :
    runP o (throwP o err : PM o α) p = some (.ok (.error err, p)) := rfl

 theorem el_throwT_run {α : Type} (err : Thrown E) (p : Parser X D CI CF) :
    runP o (throwT o err : PM o α) p = some (.error err) := rfl

 theorem el_bind_run {α β : Type} (x : PM o α) (f : α → PM o β)
    (p : Parser X D CI CF) :
    runP o (x >>= f) p =
      match runP o x p with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (.error e, q)) => some (.ok (.error e, q))
      | some (.ok (.ok a, q)) => runP o (f a) q := by
  cases h : x p with
  | none => simp only [runP, Bind.bind, ExceptT.bind, StateT.bind,
      StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h, Pure.pure, ExceptT.pure, StateT.pure]
  | some result =>
    cases result with
    | error e => simp only [runP, Bind.bind, ExceptT.bind, StateT.bind,
        StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h, ExceptT.bindCont, Pure.pure, ExceptT.pure, StateT.pure]
    | ok pair =>
      rcases pair with ⟨result, q⟩
      cases result <;>
        simp only [runP, Bind.bind, ExceptT.bind, StateT.bind,
          StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h, ExceptT.bindCont, Pure.pure, ExceptT.pure, StateT.pure]

 theorem el_observe_run {α : Type} (x : PM o α) (p : Parser X D CI CF) :
    runP o (observe o x) p =
      match runP o x p with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (result, q)) => some (.ok (.ok result, q)) := by
  cases h : x p with
  | none => simp only [runP, observe, Functor.map, ExceptT.map, tryCatchThe,
      MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind, ExceptT.bind,
      StateT.bind, StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h, Pure.pure, ExceptT.pure, StateT.pure]
  | some result =>
    cases result with
    | error e => simp only [runP, observe, Functor.map, ExceptT.map, tryCatchThe,
        MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind, ExceptT.bind,
        StateT.bind, StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h, ExceptT.bindCont, Pure.pure, ExceptT.pure, StateT.pure]
    | ok pair =>
      rcases pair with ⟨result, q⟩
      cases result <;>
        simp only [runP, observe, Functor.map, ExceptT.map, tryCatchThe,
          MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind, ExceptT.bind,
          StateT.bind, StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h, ExceptT.bindCont, Pure.pure, ExceptT.pure, StateT.pure]

 theorem el_map_run {α β : Type} (f : α → β) (x : PM o α) (p : Parser X D CI CF) :
    runP o (f <$> x) p =
      match runP o x p with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (.error e, q)) => some (.ok (.error e, q))
      | some (.ok (.ok a, q)) => some (.ok (.ok (f a), q)) := by
  cases h : x p with
  | none => simp only [runP, Functor.map, ExceptT.map, Bind.bind, ExceptT.bind,
      StateT.bind, StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h]
  | some result =>
    cases result with
    | error e => simp only [runP, Functor.map, ExceptT.map, Bind.bind, ExceptT.bind,
        StateT.bind, StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h,
        ExceptT.bindCont, Pure.pure, ExceptT.pure, StateT.pure]
    | ok pair =>
      rcases pair with ⟨result, q⟩
      cases result <;>
        simp only [runP, Functor.map, ExceptT.map, Bind.bind, ExceptT.bind,
          StateT.bind, StateT.run, ExceptT.run, ExceptT.mk, Option.bind, h,
          ExceptT.bindCont, Pure.pure, ExceptT.pure, StateT.pure]

 theorem el_discard_run {α : Type} (x : PM o α) (p : Parser X D CI CF) :
    runP o (discard x) p =
      match runP o x p with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (.error e, q)) => some (.ok (.error e, q))
      | some (.ok (.ok _, q)) => some (.ok (.ok PUnit.unit, q)) := by
  exact el_map_run o (fun _ => PUnit.unit) x p

 theorem el_get_run (p : Parser X D CI CF) :
    runP o (getP o) p = some (.ok (.ok p, p)) := rfl

 theorem el_modify_run (f : Parser X D CI CF → Parser X D CI CF)
    (p : Parser X D CI CF) :
    runP o (modifyP o f) p = some (.ok (.ok (), f p)) := rfl

 theorem el_peek_run (p : Parser X D CI CF) :
    runP o (peek o) p = some (.ok (.ok p.current_char, p)) := rfl

 theorem el_parse_error_of_tryparse (p q : Parser X D CI CF) (err : ParserError)
    (h : runP o (tryparse o) p = some (.ok (.error err, q))) :
    runP o (parse o) p = some (.error (.parserError err)) := by
  unfold parse
  rw [el_bind_run, el_observe_run, h]
  rfl

 theorem el_parse_ok_of_tryparse (p q : Parser X D CI CF) (root : TOMLDictRef)
    (h : runP o (tryparse o) p = some (.ok (.ok root, q))) :
    runP o (parse o) p = some (.ok (.ok root, q)) := by
  unfold parse
  rw [el_bind_run, el_observe_run, h]
  rfl

end
end JuliaLean.ChatGPT.Batch2.Group1


/-! ## UnicodeWhitespace -/

namespace JuliaLean.ChatGPT.Batch2.Group1
open JuliaLean JuliaLean.base.toml.parser
open JuliaLean.Proofs.base.toml.parser

set_option maxRecDepth 4096

theorem wsBytes_toList_loop (bs : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bs i acc = acc.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i acc with
  | case1 i acc h ih =>
    rw [ih, List.reverse_cons, List.append_assoc]
    have hsize : i < bs.data.toList.length := h
    rw [List.drop_eq_getElem_cons hsize]
    simp only [List.singleton_append, Array.getElem_toList]
    congr 2
    cases bs with
    | mk data => exact getElem!_pos data i h
  | case2 i acc h =>
    have hsize : bs.data.toList.length ≤ i := Nat.le_of_not_gt h
    rw [List.drop_eq_nil_of_le hsize, List.append_nil]

theorem wsBytes_toList_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [wsBytes_toList_loop]
  rfl

theorem wsBytes_characters (cs : List Char) :
    Round2.tomlWhitespaceOnly cs →
    ∀ c ∈ cs, c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' := by
  induction cs using Round2.tomlWhitespaceOnly.induct with
  | case1 =>
    intro _ c hc
    cases hc
  | case2 rest ih =>
    intro h c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact ih h c hc
  | case3 a rest hn ih =>
    intro h c hc
    have hparts : (a = ' ' ∨ a = '\t' ∨ a = '\n') ∧
        Round2.tomlWhitespaceOnly rest := by
      simpa only [Round2.tomlWhitespaceOnly, hn] using h
    rcases List.mem_cons.mp hc with rfl | hc
    · rcases hparts.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact ih hparts.2 c hc

theorem wsBytes_encode (cs : List Char)
    (hcs : ∀ c ∈ cs, c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r') :
    ∀ b ∈ cs.utf8Encode.data.toList,
      b = (9 : UInt8) ∨ b = 10 ∨ b = 13 ∨ b = 32 := by
  induction cs with
  | nil =>
    intro b hb
    change b ∈ [] at hb
    cases hb
  | cons c cs ih =>
    have hc := hcs c (List.mem_cons_self)
    have htail : ∀ c ∈ cs, c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' := by
      intro a ha
      exact hcs a (List.mem_cons_of_mem c ha)
    intro b hb
    rw [List.utf8Encode_cons, ByteArray.toList_data_append] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rcases hc with rfl | rfl | rfl | rfl
      all_goals
        obtain rfl := List.mem_singleton.mp hb
        decide
    · exact ih htail b hb

theorem wsBytes_lit (text : String) (h : Round2.tomlWhitespaceOnly text.toList) :
    ∀ b ∈ lit text, b = (9 : UInt8) ∨ b = 10 ∨ b = 13 ∨ b = 32 := by
  have hall := wsBytes_encode text.toList (wsBytes_characters text.toList h)
  simpa only [lit, String.toUTF8_eq_toByteArray, wsBytes_toList_data,
    String.utf8Encode_toList] using hall

end JuliaLean.ChatGPT.Batch2.Group1


/-! ## CharacterConstants -/

namespace JuliaLean.ChatGPT.Batch2.Group1

open JuliaLean JuliaLean.base.toml.parser

set_option maxRecDepth 4096

theorem cc_jc_space : jc ' ' = 0x20000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_tab : jc '\t' = 0x09000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_lf : jc '\n' = 0x0a000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_cr : jc '\r' = 0x0d000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_at : jc '@' = 0x40000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_equals : jc '=' = 0x3d000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_bracket : jc '[' = 0x5b000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_hash : jc '#' = 0x23000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_doublequote : jc '"' = 0x22000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_singlequote : jc '\'' = 0x27000000 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_jc_bom : jc '\ufeff' = 0xefbbbf00 := by
  unfold jc
  rw [wsBytes_toList_data]
  rfl

theorem cc_eof : EOF_CHAR = 0xffffffff := rfl

theorem cc_eof_ne_bom : (EOF_CHAR == jc '\ufeff') = false := by
  rw [cc_eof, cc_jc_bom]
  decide

end JuliaLean.ChatGPT.Batch2.Group1


/-! ## Cursor -/

namespace JuliaLean.ChatGPT.Batch2.Group1

open JuliaLean JuliaLean.base.toml.parser

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private theorem inv_int_wrap_le (n : Int) (hn : 0 ≤ n) :
    (n + 9223372036854775808) % 18446744073709551616 -
      9223372036854775808 ≤ n := by
  omega

private theorem inv_int_guard_pos (index count : Int)
    (hlo : -9223372036854775808 ≤ index)
    (hhi : index ≤ 9223372036854775807)
    (hmax : count ≤ 9223372036854775807)
    (h : (index % 18446744073709551616 - 1) % 18446744073709551616 < count) :
    0 < index := by
  omega

private theorem inv_int_unsigned_offset (index : Int) (hpos : 0 < index)
    (hmax : index ≤ 9223372036854775807) :
    (index % 18446744073709551616 - 1) % 18446744073709551616 = index - 1 := by
  omega

/-- Converting a natural byte count to the modeled signed index never increases it. -/
theorem inv_i64_nonnegative_le (z : Int) (hz : 0 ≤ z) : (i64 z).val ≤ z := by
  exact inv_int_wrap_le z hz

theorem inv_i64_nat_le (n : Nat) : (i64 (Int.ofNat n)).val ≤ (n : Int) := by
  exact inv_i64_nonnegative_le (n : Int) (Int.natCast_nonneg n)

/-- The string iterator's unsigned bounds check implies a positive signed cursor. -/
theorem inv_unsigned_guard_pos (index count : JInt64)
    (h : (JInt.rem .u64 index - JInt.lit .u64 1).val < count.val) :
    0 < index.val := by
  exact inv_int_guard_pos index.val count.val index.property.1
    index.property.2 count.property.2 h

/-- On a positive signed cursor, the unsigned guard offset is the usual predecessor. -/
theorem inv_unsigned_offset (index : JInt64) (hpos : 0 < index.val) :
    (JInt.rem .u64 index - JInt.lit .u64 1).val = index.val - 1 := by
  exact inv_int_unsigned_offset index.val hpos index.property.2

end JuliaLean.ChatGPT.Batch2.Group1


/-! ## WhitespaceTerminal -/

namespace JuliaLean.ChatGPT.Batch2.Group1

open JuliaLean JuliaLean.base.toml.parser
open JuliaLean.Proofs.base.toml.parser

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)

theorem ws_accept_eof (p : Parser X D CI CF) (f : Acc)
    (hc : p.current_char = EOF_CHAR) :
    runP o (accept o f) p = some (.ok (.ok false, p)) := by
  unfold accept
  rw [el_bind_run, el_peek_run]
  simp only [hc, BEq.rfl, Bool.false_eq_true, ↓reduceIte, el_pure_run]

theorem ws_accept_false (p : Parser X D CI CF) (f : Acc)
    (hf : (match f with | .fn g => g p.current_char | .ch c => p.current_char == c) = false) :
    runP o (accept o f) p = some (.ok (.ok false, p)) := by
  unfold accept
  rw [el_bind_run, el_peek_run]
  by_cases he : (p.current_char == EOF_CHAR) = true
  · simp only [he, Bool.false_eq_true, ↓reduceIte, el_pure_run]
  · have hef : (p.current_char == EOF_CHAR) = false := Bool.eq_false_iff.mpr he
    cases f <;> simp only [hef, hf, Bool.false_eq_true, ↓reduceIte, el_bind_run, el_pure_run]

theorem ws_accept_batch_loop_false (p : Parser X D CI CF) (f : Acc) (ok : Bool)
    (hf : (match f with | .fn g => g p.current_char | .ch c => p.current_char == c) = false) :
    runP o (accept_batch_loop o f ok) p = some (.ok (.ok ok, p)) := by
  rw [accept_batch_loop.eq_def, el_bind_run, ws_accept_false o p f hf]
  rfl

theorem ws_accept_batch_loop_eof (p : Parser X D CI CF) (f : Acc) (ok : Bool)
    (hc : p.current_char = EOF_CHAR) :
    runP o (accept_batch_loop o f ok) p = some (.ok (.ok ok, p)) := by
  rw [accept_batch_loop.eq_def, el_bind_run, ws_accept_eof o p f hc]
  rfl

theorem ws_accept_batch_eof (p : Parser X D CI CF) (f : Acc)
    (hc : p.current_char = EOF_CHAR) :
    runP o (accept_batch o f) p = some (.ok (.ok false, p)) :=
  ws_accept_batch_loop_eof o p f false hc

theorem ws_skip_comment_eof (p : Parser X D CI CF)
    (hc : p.current_char = EOF_CHAR) :
    runP o (skip_comment o) p = some (.ok (.ok false, p)) := by
  unfold skip_comment
  rw [el_bind_run, ws_accept_eof o p (chr '#') hc]
  rfl

theorem ws_skip_loop_eof (p : Parser X D CI CF) (skipped : Bool)
    (hc : p.current_char = EOF_CHAR) :
    runP o (skip_ws_nl_loop o skipped) p = some (.ok (.ok skipped, p)) := by
  rw [skip_ws_nl_loop.eq_def, el_bind_run, ws_accept_batch_eof o p _ hc]
  simp only [el_bind_run, el_discard_run, el_get_run, ws_skip_comment_eof o p hc, Bool.false_and,
    Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte, el_pure_run]

theorem ws_skip_toplevel_eof (p : Parser X D CI CF)
    (hc : p.current_char = EOF_CHAR) (hm : p.comments = none) :
    runP o (skip_ws_nl_toplevel o) p = some (.ok (.ok false, p)) := by
  unfold skip_ws_nl_toplevel
  rw [el_bind_run, el_get_run]
  simp only [hm, Option.isNone_none, Bool.false_eq_true, ↓reduceIte]
  exact ws_skip_loop_eof o p false hc

theorem ws_tryparse_eof (p : Parser X D CI CF)
    (hc : p.current_char = EOF_CHAR) (hm : p.comments = none) :
    runP o (tryparse o) p = some (.ok (.ok p.root, p)) := by
  unfold tryparse
  rw [tryparse_loop.eq_def]
  simp only [el_bind_run, el_discard_run, el_get_run, ws_skip_toplevel_eof o p hc hm, el_peek_run,
    hc, BEq.rfl, Bool.false_eq_true, ↓reduceIte, el_get_run, hm, Option.isSome_none,
    el_pure_run]

end

end JuliaLean.ChatGPT.Batch2.Group1


/-! ## Invalid -/

namespace JuliaLean.ChatGPT.Batch2.Group1

open JuliaLean JuliaLean.base.toml.parser

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- The wrapped byte count can make the installed iterator stop immediately. -/
theorem ib_iterate_none_of_nonpositive (s : Bytes) (index : JInt64)
    (hsize : (JuliaLean.Strings.ix (Int.ofNat s.length)).val ≤ 0) :
    iterateStr s index = none := by
  have hlo : 0 ≤ (JInt.rem .u64 index - JInt.lit .u64 1).val :=
    (JInt.rem .u64 index - JInt.lit .u64 1).property.1
  have hguard : ¬ (JInt.rem .u64 index - JInt.lit .u64 1).val <
      (JuliaLean.Strings.ix (Int.ofNat s.length)).val := by omega
  have hfalse : decide ((JInt.rem .u64 index - JInt.lit .u64 1).val <
      (JuliaLean.Strings.ix (s.length : Int)).val) = false := decide_eq_false hguard
  simp only [iterateStr, JuliaLean.base.strings.string.iterateString,
    hfalse, Bool.not_false, ↓reduceIte]

/-- The constructor's state before it populates its lookahead character. -/
def ib_initialParser {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (str : Bytes) : Parser X D CI CF := {
  str := str
  current_char := EOF_CHAR
  pos := i64 1
  prevpos := i64 0
  column := i64 0
  line := i64 1
  marker := i64 0
  active_table := 0
  dotted_keys := []
  chunks := []
  inline_tables := []
  static_arrays := []
  defined_tables := []
  implicit_tables := []
  root := 0
  filepath := none
  comments := none
  pending_comments := []
  captured_comment := []
  active_table_path := []
  last_item_path := none
  in_array_table := false
  tables := [o.dict.empty]
  vectors := [] }

def ib_eofParser {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (str : Bytes) : Parser X D CI CF := {
  ib_initialParser o str with
  prevpos := i64 1
  column := i64 1 }

theorem ib_new_eq_startup {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (str : Bytes) :
    Parser_new o str = runP o (startup o) (ib_initialParser o str) := by
  rfl

theorem ib_next_none {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (p : Parser X D CI CF) (h : iterateStr p.str p.pos = none) :
    runP o (next_char o) p = some (.ok (.ok EOF_CHAR,
      { p with prevpos := p.pos, column := i64 (p.column.val + 1) })) := by
  simp only [next_char, el_bind_run, el_get_run, el_modify_run, h, el_pure_run]

def ib_eatWith {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (next : PM o JChar) : PM o JChar := do
  let c := (← getP o).current_char
  let n ← next
  modifyP o fun l => { l with current_char := n }
  return c

theorem ib_eatWith_eq {X Y E D CI CF : Type} (o : Ops X Y E D CI CF) :
    eat_char o = ib_eatWith o (next_char o) := rfl

theorem ib_eatWith_step {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (next : PM o JChar) (p q : Parser X D CI CF) (c : JChar)
    (h : runP o next p = some (.ok (.ok c, q))) :
    runP o (ib_eatWith o next) p = some (.ok (.ok p.current_char,
      { q with current_char := c })) := by
  simp only [ib_eatWith, el_bind_run, el_get_run, h, el_modify_run, el_pure_run]

theorem ib_eat_step {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (p q : Parser X D CI CF) (c : JChar)
    (h : runP o (next_char o) p = some (.ok (.ok c, q))) :
    runP o (eat_char o) p = some (.ok (.ok p.current_char,
      { q with current_char := c })) := by
  rw [ib_eatWith_eq]
  exact ib_eatWith_step o (next_char o) p q c h

theorem ib_eat_none {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (p : Parser X D CI CF) (h : iterateStr p.str p.pos = none) :
    runP o (eat_char o) p = some (.ok (.ok p.current_char,
      { p with
        current_char := EOF_CHAR
        prevpos := p.pos
        column := i64 (p.column.val + 1) })) := by
  exact ib_eat_step o p _ EOF_CHAR (ib_next_none o p h)

def ib_startupWith {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (eat : PM o JChar) : PM o Unit := do
  let c ← eat
  if c == jc '\ufeff' then
    modifyP o fun l => { l with column := i64 (l.column.val - 1) }
    discard eat

theorem ib_startupWith_eq {X Y E D CI CF : Type} (o : Ops X Y E D CI CF) :
    startup o = ib_startupWith o (eat_char o) := rfl

theorem ib_startupWith_no_bom {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (eat : PM o JChar) (p q : Parser X D CI CF) (c : JChar)
    (hchar : (c == jc '\ufeff') = false)
    (h : runP o eat p = some (.ok (.ok c, q))) :
    runP o (ib_startupWith o eat) p = some (.ok (.ok (), q)) := by
  simp only [ib_startupWith, el_bind_run, h, hchar, Bool.false_eq_true, ↓reduceIte,
    el_pure_run]

theorem ib_startup_no_bom {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (p q : Parser X D CI CF)
    (hchar : (p.current_char == jc '\ufeff') = false)
    (h : runP o (eat_char o) p = some (.ok (.ok p.current_char, q))) :
    runP o (startup o) p = some (.ok (.ok (), q)) := by
  rw [ib_startupWith_eq]
  exact ib_startupWith_no_bom o (eat_char o) p q p.current_char hchar h

theorem ib_new_eof {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (str : Bytes) (h : iterateStr str (i64 1) = none) :
    Parser_new o str = some (.ok (.ok (), ib_eofParser o str)) := by
  rw [ib_new_eq_startup]
  have hnext : iterateStr (ib_initialParser o str).str
      (ib_initialParser o str).pos = none := h
  have hchar : ((ib_initialParser o str).current_char == jc '\ufeff') = false := by
    exact cc_eof_ne_bom
  exact ib_startup_no_bom o (ib_initialParser o str) (ib_eofParser o str) hchar
    (ib_eat_none o (ib_initialParser o str) hnext)

theorem ib_new_eof_of_nonpositive {X Y E D CI CF : Type}
    (o : Ops X Y E D CI CF) (str : Bytes)
    (hsize : (JuliaLean.Strings.ix (Int.ofNat str.length)).val ≤ 0) :
    Parser_new o str = some (.ok (.ok (), ib_eofParser o str)) :=
  ib_new_eof o str (ib_iterate_none_of_nonpositive str (i64 1) hsize)

theorem ib_wrapped_size_nonpositive (str : Bytes) (hsize : str.length = 2 ^ 63) :
    (JuliaLean.Strings.ix (Int.ofNat str.length)).val ≤ 0 := by
  rw [hsize]
  decide

/-- This implication diagnoses the missing representation bound without
constructing an oversized input or declaring a target refutation. -/
theorem ib_new_eof_at_wrapped_size {X Y E D CI CF : Type}
    (o : Ops X Y E D CI CF) (str : Bytes) (hsize : str.length = 2 ^ 63) :
    Parser_new o str = some (.ok (.ok (), ib_eofParser o str)) :=
  ib_new_eof_of_nonpositive o str (ib_wrapped_size_nonpositive str hsize)

end JuliaLean.ChatGPT.Batch2.Group1


/-! ## InvalidResults -/

namespace JuliaLean.ChatGPT.Batch2.Group1

open JuliaLean JuliaLean.base.toml.parser

/-- A nonpositive wrapped length makes the constructor and both public drivers
return normally with the initial root. This is a conditional model diagnosis. -/
theorem ib_drivers_root_of_nonpositive {X Y E D CI CF : Type}
    (o : Ops X Y E D CI CF) (str : Bytes)
    (hsize : (JuliaLean.Strings.ix (Int.ofNat str.length)).val ≤ 0) :
    ∃ p : Parser X D CI CF,
      Parser_new o str = some (.ok (.ok (), p)) ∧
      runP o (tryparse o) p = some (.ok (.ok 0, p)) ∧
      runP o (parse o) p = some (.ok (.ok 0, p)) := by
  let p := ib_eofParser o str
  have ht : runP o (tryparse o) p = some (.ok (.ok 0, p)) :=
    ws_tryparse_eof o p rfl rfl
  exact ⟨p, ib_new_eof_of_nonpositive o str hsize, ht,
    el_parse_ok_of_tryparse o p p 0 ht⟩

/-- The diagnosed byte length is outside the public Julia String domain. -/
theorem ib_drivers_root_at_wrapped_size {X Y E D CI CF : Type}
    (o : Ops X Y E D CI CF) (str : Bytes) (hsize : str.length = 2 ^ 63) :
    ∃ p : Parser X D CI CF,
      Parser_new o str = some (.ok (.ok (), p)) ∧
      runP o (tryparse o) p = some (.ok (.ok 0, p)) ∧
      runP o (parse o) p = some (.ok (.ok 0, p)) :=
  ib_drivers_root_of_nonpositive o str (ib_wrapped_size_nonpositive str hsize)

end JuliaLean.ChatGPT.Batch2.Group1


/-! ## EmptyLocation -/

namespace JuliaLean.ChatGPT.Batch2.Group1
open JuliaLean JuliaLean.base.toml.parser
open JuliaLean.Proofs.base.toml.parser

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

theorem el_input_bytes : lit "@\n" = [64, 10] := by
  unfold lit
  rw [wsBytes_toList_data]
  rfl

theorem el_iterate_first : iterateStr (lit "@\n") (i64 1) = some (jc '@', i64 2) := by
  rw [el_input_bytes, cc_jc_at]
  decide

theorem el_iterate_second : iterateStr (lit "@\n") (i64 2) = some (jc '\n', i64 3) := by
  rw [el_input_bytes, cc_jc_lf]
  decide

theorem el_at_not_eof : (jc '@' == EOF_CHAR) = false := by
  rw [cc_jc_at, cc_eof]
  decide

theorem el_at_not_whitespace : iswhitespace (jc '@') = false := by
  rw [iswhitespace, cc_jc_at, cc_jc_space, cc_jc_tab]
  decide

theorem el_at_not_newline : isnewline (jc '@') = false := by
  rw [isnewline, cc_jc_at, cc_jc_lf, cc_jc_cr]
  decide

theorem el_at_not_barekey : isvalid_barekey_char (jc '@') = false := by
  unfold isvalid_barekey_char
  simp only [jc, wsBytes_toList_data]
  decide

section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)

def el_decorateError (p : Parser X D CI CF) (err : ParserError) : ParserError :=
  { err with
    str := some p.str
    pos := some (i64 (p.prevpos.val - 1))
    table := some p.root
    filepath := p.filepath
    line := some p.line
    column := some (i64 (p.column.val - 1)) }

theorem el_entry_error_from_key (p q : Parser X D CI CF) (d : TOMLDictRef)
    (err : ParserError) (hkey : runP o (parse_key o) p = some (.ok (.error err, q))) :
    runP o (parse_entry o d) p = some (.ok (.error err, q)) := by
  unfold parse_entry
  rw [el_bind_run, hkey]

theorem el_toplevel_error_from_key (p q : Parser X D CI CF) (err : ParserError)
    (hbracket : runP o (accept o (chr '[')) p = some (.ok (.ok false, p)))
    (hkey : runP o (parse_key o) p = some (.ok (.error err, q))) :
    runP o (parse_toplevel o) p = some (.ok (.error err, q)) := by
  unfold parse_toplevel
  rw [el_bind_run, hbracket]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [el_bind_run, el_get_run]
  dsimp only
  rw [el_bind_run, el_entry_error_from_key o p q p.active_table err hkey]

theorem el_tryparse_error_from_toplevel (p q : Parser X D CI CF)
    (skipped : Bool) (err : ParserError)
    (hskip : runP o (skip_ws_nl_toplevel o) p = some (.ok (.ok skipped, p)))
    (hchar : (p.current_char == EOF_CHAR) = false)
    (htop : runP o (parse_toplevel o) p = some (.ok (.error err, q))) :
    runP o (tryparse o) p = some (.ok (.error (el_decorateError q err), q)) := by
  unfold tryparse
  rw [tryparse_loop.eq_def]
  simp only [el_bind_run, el_discard_run, hskip, el_peek_run, hchar, Bool.false_eq_true, ↓reduceIte]
  rw [el_observe_run, htop]
  simp only [el_get_run, el_bind_run, el_throwP_run, el_decorateError]

theorem el_accept_stops (p : Parser X D CI CF) (f : Acc)
    (hchar : (p.current_char == EOF_CHAR) = false)
    (hpred : (match f with | .fn g => g p.current_char | .ch d => p.current_char == d) = false) :
    runP o (accept o f) p = some (.ok (.ok false, p)) := by
  cases f <;> simp only at hpred
  all_goals
    simp only [accept, el_bind_run, el_peek_run, hchar, hpred,
      Bool.false_eq_true, ↓reduceIte, el_pure_run]

theorem el_batch_loop_stops (p : Parser X D CI CF) (f : Acc) (ok : Bool)
    (h : runP o (accept o f) p = some (.ok (.ok false, p))) :
    runP o (accept_batch_loop o f ok) p = some (.ok (.ok ok, p)) := by
  rw [accept_batch_loop.eq_def, el_bind_run, h]
  rfl

theorem el_batch_stops (p : Parser X D CI CF) (f : Acc)
    (h : runP o (accept o f) p = some (.ok (.ok false, p))) :
    runP o (accept_batch o f) p = some (.ok (.ok false, p)) :=
  el_batch_loop_stops o p f false h

theorem el_comment_stops (p : Parser X D CI CF)
    (h : runP o (accept o (chr '#')) p = some (.ok (.ok false, p))) :
    runP o (skip_comment o) p = some (.ok (.ok false, p)) := by
  unfold skip_comment
  rw [el_bind_run, h]
  rfl

theorem el_ws_nl_stops (p : Parser X D CI CF) (skipped : Bool)
    (hw : runP o (accept_batch o (.fn fun x => iswhitespace x || isnewline x)) p =
      some (.ok (.ok false, p)))
    (hc : runP o (skip_comment o) p = some (.ok (.ok false, p))) :
    runP o (skip_ws_nl_loop o skipped) p = some (.ok (.ok skipped, p)) := by
  rw [skip_ws_nl_loop.eq_def, el_bind_run, hw]
  dsimp only
  rw [el_bind_run, hc]
  simp only [el_bind_run, el_get_run, Bool.false_and, Bool.not_false,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte, el_pure_run]

/-- Parser state after the two-byte input has populated its first lookahead. -/
def el_inputParser : Parser X D CI CF := {
    str := lit "@\n"
    current_char := jc '@'
    pos := i64 2
    prevpos := i64 1
    column := i64 1
    line := i64 1
    marker := i64 0
    active_table := 0
    dotted_keys := []
    chunks := []
    inline_tables := []
    static_arrays := []
    defined_tables := []
    implicit_tables := []
    root := 0
    filepath := none
    comments := none
    pending_comments := []
    captured_comment := []
    active_table_path := []
    last_item_path := none
    in_array_table := false
    tables := [o.dict.empty]
    vectors := [] }

def el_afterParser : Parser X D CI CF :=
  { el_inputParser o with
    current_char := jc '\n'
    pos := i64 3
    prevpos := i64 2
    column := i64 0
    line := i64 2
    marker := i64 1 }

def el_rawError : ParserError :=
  ParserError_2 .ErrInvalidBareKeyCharacter (some (jc '@'))

theorem el_input_parser_new :
    Parser_new o (lit "@\n") = some (.ok (.ok (), el_inputParser o)) := by
  have hi := el_iterate_first
  have hb := cc_eof_ne_bom
  have hn : (jc '@' == jc '\n') = false := by rw [cc_jc_at, cc_jc_lf]; decide
  simp only [Parser_new, startup, eat_char, next_char, el_bind_run, el_get_run,
    el_modify_run, el_pure_run, hi, hb, hn, Bool.false_eq_true, ↓reduceIte,
    Option.map_none, el_inputParser]
  rfl

theorem el_input_bracket :
    runP o (accept o (chr '[')) (el_inputParser o) =
      some (.ok (.ok false, el_inputParser o)) := by
  apply el_accept_stops
  · exact el_at_not_eof
  · change (jc '@' == jc '[') = false
    rw [cc_jc_at, cc_jc_bracket]
    decide

theorem el_input_skip :
    runP o (skip_ws_nl_toplevel o) (el_inputParser o) =
      some (.ok (.ok false, el_inputParser o)) := by
  have hw : runP o (accept_batch o (.fn fun x => iswhitespace x || isnewline x))
      (el_inputParser o) = some (.ok (.ok false, el_inputParser o)) :=
    el_batch_stops o _ _ (el_accept_stops o _ _
      (by exact el_at_not_eof)
      (by change (iswhitespace (jc '@') || isnewline (jc '@')) = false
          rw [el_at_not_whitespace, el_at_not_newline]; rfl))
  have hc : runP o (skip_comment o) (el_inputParser o) =
      some (.ok (.ok false, el_inputParser o)) :=
    el_comment_stops o _ (el_accept_stops o _ _
      (by exact el_at_not_eof)
      (by change (jc '@' == jc '#') = false; rw [cc_jc_at, cc_jc_hash]; decide))
  unfold skip_ws_nl_toplevel
  rw [el_bind_run, el_get_run]
  change runP o (skip_ws_nl o) (el_inputParser o) = _
  exact el_ws_nl_stops o _ false hw hc

def el_markedParser : Parser X D CI CF :=
  { el_inputParser o with marker := i64 1 }

theorem el_marked_eat :
    runP o (eat_char o) (el_markedParser o) =
      some (.ok (.ok (jc '@'), el_afterParser o)) := by
  simp only [eat_char, next_char, el_bind_run, el_get_run, el_modify_run,
    el_pure_run, el_markedParser, el_inputParser, el_iterate_second,
    beq_self_eq_true, ↓reduceIte]
  rfl

theorem el_input_key_error :
    runP o (parse_key o) (el_inputParser o) =
      some (.ok (.error el_rawError, el_afterParser o)) := by
  have hws : runP o (skip_ws o) (el_inputParser o) =
      some (.ok (.ok false, el_inputParser o)) :=
    el_batch_stops o _ _ (el_accept_stops o _ _ el_at_not_eof el_at_not_whitespace)
  have heq : runP o (accept o (chr '=')) (el_inputParser o) =
      some (.ok (.ok false, el_inputParser o)) :=
    el_accept_stops o _ _ el_at_not_eof
      (by change (jc '@' == jc '=') = false; rw [cc_jc_at, cc_jc_equals]; decide)
  have hdq : runP o (accept o (chr '"')) (el_inputParser o) =
      some (.ok (.ok false, el_inputParser o)) :=
    el_accept_stops o _ _ el_at_not_eof
      (by change (jc '@' == jc '"') = false; rw [cc_jc_at, cc_jc_doublequote]; decide)
  have hsq : runP o (accept o (chr '\'')) (el_inputParser o) =
      some (.ok (.ok false, el_inputParser o)) :=
    el_accept_stops o _ _ el_at_not_eof
      (by change (jc '@' == jc '\'') = false; rw [cc_jc_at, cc_jc_singlequote]; decide)
  have hmark : runP o (set_marker o) (el_inputParser o) =
      some (.ok (.ok (), el_markedParser o)) := rfl
  have hbare : runP o (accept_batch o (.fn isvalid_barekey_char)) (el_markedParser o) =
      some (.ok (.ok false, el_markedParser o)) :=
    el_batch_stops o _ _ (el_accept_stops o _ _ el_at_not_eof el_at_not_barekey)
  have hkeys : (el_inputParser o).dotted_keys.isEmpty = true := rfl
  unfold parse_key
  rw [el_bind_run, el_modify_run]
  change runP o (_parse_key o) (el_inputParser o) = _
  rw [_parse_key.eq_def]
  simp only [el_bind_run, el_discard_run, hws, el_get_run, hkeys, heq, hdq, hsq,
    hmark, hbare, el_marked_eat, el_throwP_run, Bool.false_eq_true,
    ↓reduceIte]
  rfl

theorem el_input_tryparse :
    runP o (tryparse o) (el_inputParser o) =
      some (.ok (.error (el_decorateError (el_afterParser o) el_rawError),
        el_afterParser o)) := by
  apply el_tryparse_error_from_toplevel o _ _ false el_rawError
  · exact el_input_skip o
  · exact el_at_not_eof
  · exact el_toplevel_error_from_key o _ _ _ (el_input_bracket o) (el_input_key_error o)

end

/-- The unused external operations do not affect either counterexample path. -/
def el_exampleDict {K V : Type} : DictOps K V Unit := {
  empty := ()
  get := fun _ _ => none
  set := fun _ _ _ => ()
  isempty := fun _ => true
  emptyBang := fun _ => ()
  eq := fun _ _ _ => true
  pairs := fun _ => []
  delete := fun _ _ => () }

def el_exampleOps : Ops Unit Unit Unit Unit Unit Unit := {
  dict := el_exampleDict
  items := el_exampleDict
  floating := el_exampleDict
  dates := none
  parse_Int64 := fun _ _ => .error (.ext ())
  parse_UInt64 := fun _ _ => .error (.ext ())
  parse_Int128 := fun _ _ => .error (.ext ())
  parse_UInt128 := fun _ _ => .error (.ext ())
  parse_BigInt := fun _ _ => .error (.ext ())
  tryparse_Float64 := fun _ => .ok none
  unescape_string := fun s => .ok s
  escape_string := fun s => .ok s
  string_Char := fun _ => []
  substring := fun _ _ _ => .ok []
  prevind := fun _ i => .ok (i64 (i.val - 1))
  length := fun s => i64 s.length
  filter_underscore := fun s => s
  pow_Int := fun _ _ => .error (.ext ())
  readString := fun _ => .error (.ext ()) }

/-- The two-byte public Julia counterexample is an invalid key followed by LF. -/
theorem TomlR1TryparseErrorLocation_refuted :
    ¬ JuliaLean.Proofs.base.toml.parser.Round2.TryparseInvalidInitialBareKeyLocation := by
  intro h
  have hnew : Parser_new el_exampleOps (lit (String.singleton '@' ++ "\n")) =
      some (.ok (.ok (), el_inputParser el_exampleOps)) := by
    exact el_input_parser_new el_exampleOps
  obtain ⟨after, err, hr, _, hline, _⟩ :=
    h el_exampleOps "\n" (el_inputParser el_exampleOps) hnew
  have hp := Except.ok.inj (Option.some.inj ((el_input_tryparse el_exampleOps).symm.trans hr))
  have he := Except.error.inj (congrArg Prod.fst hp)
  rw [← he] at hline
  have hbad : (i64 2) = i64 1 := Option.some.inj hline
  exact (by decide : i64 2 ≠ i64 1) hbad

/-- The throwing API preserves the same incorrect line location. -/
theorem TomlR1ParseErrorLocation_refuted :
    ¬ JuliaLean.Proofs.base.toml.parser.Round2.ParseInvalidInitialBareKeyLocation := by
  intro h
  have hnew : Parser_new el_exampleOps (lit (String.singleton '@' ++ "\n")) =
      some (.ok (.ok (), el_inputParser el_exampleOps)) := by
    exact el_input_parser_new el_exampleOps
  obtain ⟨err, hr, _, hline, _⟩ :=
    h el_exampleOps "\n" (el_inputParser el_exampleOps) hnew
  have hparse := el_parse_error_of_tryparse el_exampleOps _ _ _ (el_input_tryparse el_exampleOps)
  have he := Thrown.parserError.inj (Except.error.inj (Option.some.inj (hparse.symm.trans hr)))
  rw [← he] at hline
  have hbad : (i64 2) = i64 1 := Option.some.inj hline
  exact (by decide : i64 2 ≠ i64 1) hbad

end JuliaLean.ChatGPT.Batch2.Group1


/-! ## Whitespace -/

namespace JuliaLean.ChatGPT.Batch2.Group1

open JuliaLean JuliaLean.base.toml.parser
open JuliaLean.Proofs.base.toml.parser

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000


/-- The four bytes accepted by the parser's whitespace scan. -/
def wsByteGood (b : UInt8) : Prop := b = 9 ∨ b = 10 ∨ b = 13 ∨ b = 32

def wsCharGood (c : JChar) : Prop :=
  c = jc ' ' ∨ c = jc '\t' ∨ c = jc '\n' ∨ c = jc '\r'

def wsCurrentGood (c : JChar) : Prop := c = EOF_CHAR ∨ wsCharGood c

theorem ws_byte_good (b : UInt8) (hb : wsByteGood b) :
    JuliaLean.base.strings.string.between (· ≤ ·) b 0x80 0xf7 = false ∧
    wsCharGood (b.toUInt32 <<< 24) := by
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [wsCharGood, cc_jc_space, cc_jc_tab, cc_jc_lf, cc_jc_cr] <;> decide

theorem ws_char_flags (c : JChar) (hc : wsCharGood c) :
    (c == EOF_CHAR) = false ∧ (iswhitespace c || isnewline c) = true ∧ c ≠ EOF_CHAR := by
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [iswhitespace, isnewline, cc_eof, cc_jc_space, cc_jc_tab, cc_jc_lf, cc_jc_cr] <;> decide

theorem ws_getD_mem {α : Type} (xs : List α) (k : Nat) (d : α) (hk : k < xs.length) :
    xs.getD k d ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

theorem ws_iterate_some (bs : Bytes) (i : JInt64) (c : JChar) (j : JInt64)
    (hb : ∀ b ∈ bs, wsByteGood b) (hit : iterateStr bs i = some (c, j)) :
    wsCharGood c ∧ j = i + JuliaLean.Strings.ix 1 ∧ 0 < i.val := by
  by_cases hg : (JInt.rem .u64 i - JInt.lit .u64 1).val < (JuliaLean.Strings.ix bs.length).val
  · have hp := inv_unsigned_guard_pos i (JuliaLean.Strings.ix bs.length) hg
    have hoff := inv_unsigned_offset i hp
    have hn := inv_i64_nat_le bs.length
    have hk : i.val.toNat - 1 < bs.length := by
      rw [hoff] at hg
      change (JuliaLean.Strings.ix (bs.length : Int)).val ≤ (bs.length : Int) at hn
      omega
    have hbyte := ws_byte_good (bs.getD (i.val.toNat - 1) 0)
      (hb _ (ws_getD_mem bs _ 0 hk))
    have hdec : decide ((JInt.rem .u64 i - JInt.lit .u64 1).val <
        (JuliaLean.Strings.ix (bs.length : Int)).val) = true := decide_eq_true hg
    unfold iterateStr JuliaLean.base.strings.string.iterateString at hit
    simp only [hdec, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbyte.1, Bool.not_false] at hit
    obtain ⟨hc, hj⟩ := Prod.mk.inj (Option.some.inj hit)
    exact ⟨hc ▸ hbyte.2, hj.symm, hp⟩
  · have hdec : decide ((JInt.rem .u64 i - JInt.lit .u64 1).val <
        (JuliaLean.Strings.ix (bs.length : Int)).val) = false := decide_eq_false hg
    unfold iterateStr JuliaLean.base.strings.string.iterateString at hit
    simp only [hdec, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hit
    cases hit

def wsRankPos (pos : JInt64) : Nat :=
  if 0 < pos.val then (2 ^ 63 - pos.val).toNat else 0

theorem ws_rank_step (pos : JInt64) (hp : 0 < pos.val) :
    wsRankPos (pos + JuliaLean.Strings.ix 1) < wsRankPos pos := by
  have hmax := pos.property.2
  change pos.val ≤ 9223372036854775807 at hmax
  by_cases hlt : pos.val < 9223372036854775807
  · have hv : (pos + JuliaLean.Strings.ix 1).val = pos.val + 1 := by
      change wrapInt .i64 (pos.val + 1) = pos.val + 1
      apply wrapInt_of_inRange
      change -9223372036854775808 ≤ pos.val + 1 ∧ pos.val + 1 ≤ 9223372036854775807
      omega
    unfold wsRankPos
    rw [if_pos hp, hv, if_pos (by omega)]
    omega
  · have hv : pos.val = 9223372036854775807 := by omega
    have hs : (pos + JuliaLean.Strings.ix 1).val = -9223372036854775808 := by
      change wrapInt .i64 (pos.val + 1) = -9223372036854775808
      rw [hv]
      rfl
    unfold wsRankPos
    rw [if_pos hp, hs, if_neg (by decide), hv]
    decide

section
variable {X Y E D CI CF : Type}

def wsAfterWith (p : Parser X D CI CF) (state : Option (JChar × JInt64)) : Parser X D CI CF :=
  let q := { p with prevpos := p.pos, column := i64 (p.column.val + 1) }
  match state with
  | none => { q with current_char := EOF_CHAR }
  | some (c, pos) =>
    let q := { q with pos := pos, current_char := c }
    if c == jc '\n' then { q with line := i64 (p.line.val + 1), column := i64 0 }
    else q

def wsAfter (p : Parser X D CI CF) : Parser X D CI CF :=
  wsAfterWith p (iterateStr p.str p.pos)

def wsRank (p : Parser X D CI CF) : Nat :=
  if p.current_char = EOF_CHAR then 0 else wsRankPos p.pos + 1

theorem ws_afterWith_str (p : Parser X D CI CF) (state : Option (JChar × JInt64)) :
    (wsAfterWith p state).str = p.str := by
  cases state with
  | none => rfl
  | some pair =>
    rcases pair with ⟨c, j⟩
    dsimp only [wsAfterWith]
    split <;> rfl

theorem ws_after_str (p : Parser X D CI CF) : (wsAfter p).str = p.str :=
  ws_afterWith_str p _

theorem ws_afterWith_comments (p : Parser X D CI CF) (state : Option (JChar × JInt64)) :
    (wsAfterWith p state).comments = p.comments := by
  cases state with
  | none => rfl
  | some pair =>
    rcases pair with ⟨c, j⟩
    dsimp only [wsAfterWith]
    split <;> rfl

theorem ws_after_comments (p : Parser X D CI CF) : (wsAfter p).comments = p.comments :=
  ws_afterWith_comments p _

theorem ws_afterWith_good (p : Parser X D CI CF) (state : Option (JChar × JInt64))
    (hstate : ∀ c j, state = some (c, j) → wsCharGood c) :
    wsCurrentGood (wsAfterWith p state).current_char := by
  cases state with
  | none => exact Or.inl rfl
  | some pair =>
    rcases pair with ⟨c, j⟩
    have hc := hstate c j rfl
    dsimp only [wsAfterWith]
    split <;> exact Or.inr hc

theorem ws_after_good (p : Parser X D CI CF) (hb : ∀ b ∈ p.str, wsByteGood b) :
    wsCurrentGood (wsAfter p).current_char := by
  apply ws_afterWith_good p (iterateStr p.str p.pos)
  intro c j hit
  exact (ws_iterate_some p.str p.pos c j hb hit).1

theorem ws_afterWith_rank (p : Parser X D CI CF) (state : Option (JChar × JInt64))
    (hne : p.current_char ≠ EOF_CHAR)
    (hstate : ∀ c j, state = some (c, j) → c ≠ EOF_CHAR ∧ wsRankPos j < wsRankPos p.pos) :
    wsRank (wsAfterWith p state) < wsRank p := by
  cases state with
  | none =>
    simp only [wsAfterWith, wsRank, hne, ↓reduceIte]
    omega
  | some pair =>
    rcases pair with ⟨c, j⟩
    obtain ⟨hne', hlt⟩ := hstate c j rfl
    dsimp only [wsAfterWith]
    split <;> simp only [wsRank, hne, hne', ↓reduceIte] <;> omega

theorem ws_after_rank (p : Parser X D CI CF) (hb : ∀ b ∈ p.str, wsByteGood b)
    (hc : wsCharGood p.current_char) : wsRank (wsAfter p) < wsRank p := by
  apply ws_afterWith_rank p (iterateStr p.str p.pos) (ws_char_flags p.current_char hc).2.2
  intro c j hit
  obtain ⟨hgood, hj, hp⟩ := ws_iterate_some p.str p.pos c j hb hit
  refine ⟨(ws_char_flags c hgood).2.2, ?_⟩
  rw [hj]
  exact ws_rank_step p.pos hp

theorem wr_next_some (o : Ops X Y E D CI CF) (p : Parser X D CI CF)
    (c : JChar) (pos : JInt64) (h : iterateStr p.str p.pos = some (c, pos)) :
    runP o (next_char o) p = some (.ok (.ok c,
      if c == jc '\n' then
        { p with
          prevpos := p.pos
          pos := pos
          line := i64 (p.line.val + 1)
          column := i64 0 }
      else
        { p with
          prevpos := p.pos
          pos := pos
          column := i64 (p.column.val + 1) })) := by
  cases hc : c == jc '\n' <;>
    simp only [next_char, el_bind_run, el_get_run, el_modify_run, h, hc,
      Bool.false_eq_true, ↓reduceIte, el_pure_run]

theorem wr_eat_for_state (o : Ops X Y E D CI CF) (p : Parser X D CI CF)
    (state : Option (JChar × JInt64)) (hit : iterateStr p.str p.pos = state) :
    runP o (eat_char o) p = some (.ok (.ok p.current_char, wsAfterWith p state)) := by
  cases state with
  | none => exact ib_eat_none o p hit
  | some pair =>
    rcases pair with ⟨c, pos⟩
    have hn := wr_next_some o p c pos hit
    have he := ib_eat_step o p _ c hn
    cases hc : c == jc '\n' <;>
      simpa only [wsAfterWith, hc, Bool.false_eq_true, ↓reduceIte] using he

def wr_acceptWith (o : Ops X Y E D CI CF) (eat : PM o JChar) (f : Acc) : PM o Bool := do
  let c ← peek o
  if c == EOF_CHAR then return false
  let ok := match f with
    | .fn g => g c
    | .ch d => c == d
  if ok then discard eat
  return ok

theorem wr_acceptWith_eq (o : Ops X Y E D CI CF) (f : Acc) :
    accept o f = wr_acceptWith o (eat_char o) f := rfl

theorem wr_acceptWith_yes (o : Ops X Y E D CI CF) (eat : PM o JChar) (f : Acc)
    (p q : Parser X D CI CF) (value : JChar)
    (heof : (p.current_char == EOF_CHAR) = false)
    (hpred : (match f with | .fn g => g p.current_char | .ch d => p.current_char == d) = true)
    (heat : runP o eat p = some (.ok (.ok value, q))) :
    runP o (wr_acceptWith o eat f) p = some (.ok (.ok true, q)) := by
  cases f <;>
    simp only [wr_acceptWith, el_bind_run, el_peek_run, heof, hpred,
      Bool.false_eq_true, ↓reduceIte, el_discard_run, heat, el_pure_run]

theorem wr_accept_yes (o : Ops X Y E D CI CF) (f : Acc)
    (p q : Parser X D CI CF) (value : JChar)
    (heof : (p.current_char == EOF_CHAR) = false)
    (hpred : (match f with | .fn g => g p.current_char | .ch d => p.current_char == d) = true)
    (heat : runP o (eat_char o) p = some (.ok (.ok value, q))) :
    runP o (accept o f) p = some (.ok (.ok true, q)) := by
  rw [wr_acceptWith_eq]
  exact wr_acceptWith_yes o (eat_char o) f p q value heof hpred heat


theorem ws_eat_run (o : Ops X Y E D CI CF) (p : Parser X D CI CF) :
    runP o (eat_char o) p = some (.ok (.ok p.current_char, wsAfter p)) := by
  exact wr_eat_for_state o p (iterateStr p.str p.pos) rfl



theorem ws_accept_good (o : Ops X Y E D CI CF) (p : Parser X D CI CF)
    (hc : wsCharGood p.current_char) :
    runP o (accept o (.fn fun c => iswhitespace c || isnewline c)) p =
      some (.ok (.ok true, wsAfter p)) := by
  have hf := ws_char_flags p.current_char hc
  exact wr_accept_yes o (.fn fun c => iswhitespace c || isnewline c)
    p (wsAfter p) p.current_char hf.1 hf.2.1 (ws_eat_run o p)


theorem ws_batch_to_eof (o : Ops X Y E D CI CF) (p : Parser X D CI CF) (ok : Bool)
    (hb : ∀ b ∈ p.str, wsByteGood b) (hc : wsCurrentGood p.current_char) :
    ∃ q done, runP o (accept_batch_loop o (.fn fun c => iswhitespace c || isnewline c) ok) p =
      some (.ok (.ok done, q)) ∧ q.current_char = EOF_CHAR ∧ q.comments = p.comments := by
  have main : ∀ n : Nat, ∀ (p : Parser X D CI CF), wsRank p = n → ∀ (ok : Bool),
      (∀ b ∈ p.str, wsByteGood b) → wsCurrentGood p.current_char →
      ∃ q done, runP o (accept_batch_loop o (.fn fun c => iswhitespace c || isnewline c) ok) p =
        some (.ok (.ok done, q)) ∧ q.current_char = EOF_CHAR ∧ q.comments = p.comments := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p hn ok hb hc
      rcases hc with heof | hwhite
      · exact ⟨p, ok, ws_accept_batch_loop_eof o p _ ok heof, heof, rfl⟩
      · have hless : wsRank (wsAfter p) < n := by
          rw [← hn]
          exact ws_after_rank p hb hwhite
        have hbnext : ∀ b ∈ (wsAfter p).str, wsByteGood b := by
          simpa only [ws_after_str] using hb
        obtain ⟨q, done, hrun, heof, hcomments⟩ :=
          ih (wsRank (wsAfter p)) hless (wsAfter p) rfl true hbnext (ws_after_good p hb)
        refine ⟨q, done, ?_, heof, hcomments.trans (ws_after_comments p)⟩
        rw [accept_batch_loop.eq_def, el_bind_run, ws_accept_good o p hwhite]
        exact hrun
  exact main (wsRank p) p rfl ok hb hc

theorem ws_skip_to_eof (o : Ops X Y E D CI CF) (p : Parser X D CI CF) (skipped : Bool)
    (hb : ∀ b ∈ p.str, wsByteGood b) (hc : wsCurrentGood p.current_char) :
    ∃ q done, runP o (skip_ws_nl_loop o skipped) p = some (.ok (.ok done, q)) ∧
      q.current_char = EOF_CHAR ∧ q.comments = p.comments := by
  obtain ⟨q, done, hrun, heof, hcomments⟩ := ws_batch_to_eof o p false hb hc
  change runP o (accept_batch o (.fn fun c => iswhitespace c || isnewline c)) p = _ at hrun
  cases done with
  | false =>
    refine ⟨q, skipped, ?_, heof, hcomments⟩
    rw [skip_ws_nl_loop.eq_def, el_bind_run, hrun]
    simp only [el_bind_run, el_discard_run, el_get_run, ws_skip_comment_eof o q heof, Bool.false_and,
      Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte, el_pure_run]
  | true =>
    refine ⟨q, true, ?_, heof, hcomments⟩
    rw [skip_ws_nl_loop.eq_def, el_bind_run, hrun]
    simp only [el_bind_run, el_discard_run, el_get_run, ws_skip_comment_eof o q heof, Bool.false_and,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, el_pure_run]
    exact ws_skip_loop_eof o q true heof

theorem ws_tryparse_white (o : Ops X Y E D CI CF) (p : Parser X D CI CF)
    (hb : ∀ b ∈ p.str, wsByteGood b) (hc : wsCurrentGood p.current_char)
    (hm : p.comments = none) :
    ∃ q, runP o (tryparse o) p = some (.ok (.ok q.root, q)) := by
  obtain ⟨q, done, hrun, heof, hcomments⟩ := ws_skip_to_eof o p false hb hc
  have hmq : q.comments = none := hcomments.trans hm
  have hskip : runP o (skip_ws_nl_toplevel o) p = some (.ok (.ok done, q)) := by
    unfold skip_ws_nl_toplevel
    rw [el_bind_run, el_get_run]
    simp only [hm, Option.isNone_none, Bool.false_eq_true, ↓reduceIte]
    exact hrun
  refine ⟨q, ?_⟩
  unfold tryparse
  rw [tryparse_loop.eq_def]
  simp only [el_bind_run, el_discard_run, el_get_run, hskip, el_peek_run, heof, BEq.rfl, Bool.false_eq_true, ↓reduceIte,
    el_get_run, hmq, Option.isSome_none, el_pure_run]


theorem ws_new_after (o : Ops X Y E D CI CF) (str : Bytes) :
    Parser_new o str = some (.ok (.ok (), wsAfter (ib_initialParser o str))) := by
  rw [ib_new_eq_startup]
  exact ib_startup_no_bom o (ib_initialParser o str) _ cc_eof_ne_bom
    (ws_eat_run o (ib_initialParser o str))



theorem ws_new_fields (o : Ops X Y E D CI CF) (str : Bytes)
    (p : Parser X D CI CF) (hb : ∀ b ∈ str, wsByteGood b)
    (hnew : Parser_new o str = some (.ok (.ok (), p))) :
    p.str = str ∧ p.comments = none ∧ wsCurrentGood p.current_char := by
  rw [ws_new_after] at hnew
  have heq : wsAfter (ib_initialParser o str) = p := by
    exact (Prod.mk.inj (Except.ok.inj (Option.some.inj hnew))).2
  rw [← heq]
  refine ⟨ws_after_str _, ws_after_comments _, ws_after_good _ hb⟩


theorem TomlR1TryparseWhitespaceRoot_proven :
    JuliaLean.Proofs.base.toml.parser.Round2.TryparseWhitespaceOnlyReturnsRoot := by
  intro X Y E D CI CF o text p hwhite hnew
  have hb : ∀ b ∈ lit text, wsByteGood b := wsBytes_lit text hwhite
  obtain ⟨hstr, hcomments, hcurrent⟩ := ws_new_fields o (lit text) p hb hnew
  have hbp : ∀ b ∈ p.str, wsByteGood b := by simpa only [hstr] using hb
  obtain ⟨q, hrun⟩ := ws_tryparse_white o p hbp hcurrent hcomments
  exact ⟨q, q.root, hrun, rfl⟩

theorem TomlR1ParseWhitespaceRoot_proven :
    JuliaLean.Proofs.base.toml.parser.Round2.ParseWhitespaceOnlyReturnsRoot := by
  intro X Y E D CI CF o text p hwhite hnew
  obtain ⟨q, root, hrun, hroot⟩ := TomlR1TryparseWhitespaceRoot_proven o text p hwhite hnew
  exact ⟨q, root, el_parse_ok_of_tryparse o p q root hrun, hroot⟩

end
end JuliaLean.ChatGPT.Batch2.Group1
end JuliaLean.Proofs.base.toml.parser

set_option maxRecDepth 4096
namespace JuliaLean.ChatGPT.Batch3.Group4
open JuliaLean JuliaLean.base.toml.parser
open JuliaLean.Proofs.base.toml.parser
open JuliaLean.Proofs.base.toml.parser.JuliaLean.ChatGPT.Batch2.Group1

theorem TomlByteList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have loop : ∀ (i : Nat) (acc : List UInt8),
      ByteArray.toList.loop bs i acc = acc.reverse ++ bs.data.toList.drop i := by
    intro i acc
    fun_induction ByteArray.toList.loop bs i acc with
    | case1 i acc h ih =>
      rw [ih, List.reverse_cons, List.append_assoc]
      have hsize : i < bs.data.toList.length := h
      rw [List.drop_eq_getElem_cons hsize]
      simp only [List.singleton_append, Array.getElem_toList]
      congr 2
      cases bs with
      | mk data => exact getElem!_pos data i h
    | case2 i acc h =>
      have hsize : bs.data.toList.length ≤ i := Nat.le_of_not_gt h
      rw [List.drop_eq_nil_of_le hsize, List.append_nil]
  unfold ByteArray.toList
  rw [loop]
  rfl


theorem TomlLitAppend (s t : String) : lit (s ++ t) = lit s ++ lit t := by
  simp only [lit, String.toUTF8_eq_toByteArray, TomlByteList, String.toByteArray_append,
    ByteArray.toList_data_append]

theorem TomlLitSingleton (c : Char) : lit (String.singleton c) = String.utf8EncodeChar c := by
  simp only [lit, String.toUTF8_eq_toByteArray, TomlByteList, String.toByteArray_singleton,
    List.utf8Encode_singleton, List.toList_data_toByteArray]

theorem TomlLitLength (s : String) : (lit s).length = s.utf8ByteSize := by
  simp only [lit, String.toUTF8_eq_toByteArray, TomlByteList, Array.length_toList]
  rfl

def TomlPack (a b c d : UInt8) : UInt32 :=
  (a.toUInt32 <<< 24) ||| ((b.toUInt32 <<< 16) ||| ((c.toUInt32 <<< 8) ||| d.toUInt32))

theorem TomlShift24 (b : UInt8) : (b.toUInt32 <<< 24).toNat = b.toNat * 16777216 := by
  have hb := b.toNat_lt
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  change (b.toNat <<< 24) % 4294967296 = _
  rw [Nat.shiftLeft_eq]
  omega

theorem TomlShift16 (b : UInt8) : (b.toUInt32 <<< 16).toNat = b.toNat * 65536 := by
  have hb := b.toNat_lt
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  change (b.toNat <<< 16) % 4294967296 = _
  rw [Nat.shiftLeft_eq]
  omega

theorem TomlShift8 (b : UInt8) : (b.toUInt32 <<< 8).toNat = b.toNat * 256 := by
  have hb := b.toNat_lt
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  change (b.toNat <<< 8) % 4294967296 = _
  rw [Nat.shiftLeft_eq]
  omega

theorem TomlPackNat (a b c d : UInt8) : (TomlPack a b c d).toNat =
    a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat := by
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have e1 : (c.toNat * 256 ||| d.toNat) = c.toNat * 256 + d.toNat := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 8) hd c.toNat
    simpa only [Nat.reducePow, Nat.mul_comm] using h.symm
  have e2 : (b.toNat * 65536 ||| (c.toNat * 256 + d.toNat)) =
      b.toNat * 65536 + (c.toNat * 256 + d.toNat) := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 16)
      (show c.toNat * 256 + d.toNat < 2 ^ 16 by omega) b.toNat
    simpa only [Nat.reducePow, Nat.mul_comm] using h.symm
  have e3 : (a.toNat * 16777216 ||| (b.toNat * 65536 + (c.toNat * 256 + d.toNat))) =
      a.toNat * 16777216 + (b.toNat * 65536 + (c.toNat * 256 + d.toNat)) := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 24)
      (show b.toNat * 65536 + (c.toNat * 256 + d.toNat) < 2 ^ 24 by omega) a.toNat
    simpa only [Nat.reducePow, Nat.mul_comm] using h.symm
  simp only [TomlPack, UInt32.toNat_or, TomlShift24, TomlShift16, TomlShift8,
    UInt8.toNat_toUInt32, e1, e2, e3]
  omega

theorem TomlJcOne (c : Char) (a : UInt8) (h : String.utf8EncodeChar c = [a]) :
    jc c = TomlPack a 0 0 0 := by
  have hb := TomlLitSingleton c
  change (String.singleton c).toUTF8.toList = _ at hb
  unfold jc
  rw [hb, h]
  change ((0 : UInt32) ||| (a.toUInt32 <<< 24)) = TomlPack a 0 0 0
  simp only [TomlPack, UInt32.zero_or, UInt32.or_zero, show (0 : UInt8).toUInt32 = (0 : UInt32) from rfl, UInt32.zero_shiftLeft]


theorem TomlJcTwo (c : Char) (a b : UInt8) (h : String.utf8EncodeChar c = [a,b]) :
    jc c = TomlPack a b 0 0 := by
  have hb := TomlLitSingleton c
  change (String.singleton c).toUTF8.toList = _ at hb
  unfold jc
  rw [hb, h]
  change (((0 : UInt32) ||| (a.toUInt32 <<< 24)) ||| (b.toUInt32 <<< 16)) = TomlPack a b 0 0
  simp only [TomlPack, UInt32.zero_or, UInt32.or_zero, show (0 : UInt8).toUInt32 = (0 : UInt32) from rfl, UInt32.zero_shiftLeft]


theorem TomlJcThree (c : Char) (a b d : UInt8) (h : String.utf8EncodeChar c = [a,b,d]) :
    jc c = TomlPack a b d 0 := by
  have hb := TomlLitSingleton c
  change (String.singleton c).toUTF8.toList = _ at hb
  unfold jc
  rw [hb, h]
  change ((((0 : UInt32) ||| (a.toUInt32 <<< 24)) ||| (b.toUInt32 <<< 16)) ||| (d.toUInt32 <<< 8)) = TomlPack a b d 0
  simp only [TomlPack, UInt32.zero_or, UInt32.or_zero, show (0 : UInt8).toUInt32 = (0 : UInt32) from rfl, UInt32.or_assoc]


theorem TomlJcFour (c : Char) (a b d e : UInt8) (h : String.utf8EncodeChar c = [a,b,d,e]) :
    jc c = TomlPack a b d e := by
  have hb := TomlLitSingleton c
  change (String.singleton c).toUTF8.toList = _ at hb
  unfold jc
  rw [hb, h]
  change (((((0 : UInt32) ||| (a.toUInt32 <<< 24)) ||| (b.toUInt32 <<< 16)) ||| (d.toUInt32 <<< 8)) ||| (e.toUInt32 <<< 0)) = TomlPack a b d e
  simp only [TomlPack, UInt32.zero_or, UInt32.shiftLeft_zero, UInt32.or_assoc]

def TomlByte (n : Nat) : UInt8 := UInt8.ofNat n

theorem TomlByteNat (n : Nat) (h : n < 256) : (TomlByte n).toNat = n := by
  simp only [TomlByte, UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem TomlJcAscii (c : Char) (h : c.val.toNat ≤ 127) :
    (jc c).toNat = c.val.toNat * 16777216 := by
  have he : String.utf8EncodeChar c = [TomlByte c.val.toNat] := by
    simp only [String.utf8EncodeChar, h, ↓reduceIte, TomlByte]
  rw [TomlJcOne c _ he, TomlPackNat, TomlByteNat _ (by omega)]
  simp only [show (0 : UInt8).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem TomlJcNotAscii (c : Char) (h : 127 < c.val.toNat) :
    3221225472 ≤ (jc c).toNat ∧ (jc c).toNat < 4160749568 := by
  have hn : ¬ c.val.toNat ≤ 127 := by omega
  by_cases htwo : c.val.toNat ≤ 2047
  · have he : String.utf8EncodeChar c =
        [TomlByte (c.val.toNat / 64 % 32 + 192), TomlByte (c.val.toNat % 64 + 128)] := by
      simp only [String.utf8EncodeChar, hn, htwo, ↓reduceIte, TomlByte]
    rw [TomlJcTwo c _ _ he, TomlPackNat, TomlByteNat _ (by omega), TomlByteNat _ (by omega)]
    change 3221225472 ≤ (c.val.toNat / 64 % 32 + 192) * 16777216 +
      (c.val.toNat % 64 + 128) * 65536 + 0 * 256 + 0 ∧ _
    simp only [show (0 : UInt8).toNat = 0 from rfl] at *
    omega
  · by_cases hthree : c.val.toNat ≤ 65535
    · have he : String.utf8EncodeChar c =
          [TomlByte (c.val.toNat / 4096 % 16 + 224), TomlByte (c.val.toNat / 64 % 64 + 128),
            TomlByte (c.val.toNat % 64 + 128)] := by
        simp only [String.utf8EncodeChar, hn, htwo, hthree, ↓reduceIte, TomlByte]
      rw [TomlJcThree c _ _ _ he, TomlPackNat, TomlByteNat _ (by omega), TomlByteNat _ (by omega),
        TomlByteNat _ (by omega)]
      change 3221225472 ≤ (c.val.toNat / 4096 % 16 + 224) * 16777216 +
        (c.val.toNat / 64 % 64 + 128) * 65536 + (c.val.toNat % 64 + 128) * 256 + 0 ∧ _
      simp only [show (0 : UInt8).toNat = 0 from rfl] at *
      omega
    · have he : String.utf8EncodeChar c =
          [TomlByte (c.val.toNat / 262144 % 8 + 240), TomlByte (c.val.toNat / 4096 % 64 + 128),
            TomlByte (c.val.toNat / 64 % 64 + 128), TomlByte (c.val.toNat % 64 + 128)] := by
        simp only [String.utf8EncodeChar, hn, htwo, hthree, ↓reduceIte, TomlByte]
      rw [TomlJcFour c _ _ _ _ he, TomlPackNat, TomlByteNat _ (by omega), TomlByteNat _ (by omega),
        TomlByteNat _ (by omega), TomlByteNat _ (by omega)]
      omega

theorem TomlJcNeEof (c : Char) : jc c ≠ (0xffffffff : UInt32) := by
  intro heq
  have he := congrArg UInt32.toNat heq
  change (jc c).toNat = 4294967295 at he
  by_cases hc : c.val.toNat ≤ 127
  · rw [TomlJcAscii c hc] at he
    omega
  · have hb := (TomlJcNotAscii c (by omega)).2
    omega

theorem TomlJcAsciiInjective (c d : Char) (hd : d.val.toNat ≤ 127)
    (h : jc c = jc d) : c = d := by
  have he := congrArg UInt32.toNat h
  rw [TomlJcAscii d hd] at he
  by_cases hc : c.val.toNat ≤ 127
  · rw [TomlJcAscii c hc] at he
    apply Char.val_inj.mp
    apply UInt32.toNat_inj.mp
    omega
  · have hb := (TomlJcNotAscii c (by omega)).1
    omega



theorem TomlPackOne (a : UInt8) : TomlPack a 0 0 0 = a.toUInt32 <<< 24 := by
  apply UInt32.toNat_inj.mp
  rw [TomlPackNat, TomlShift24]
  simp only [show (0 : UInt8).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem TomlPackTwo (a b : UInt8) :
    TomlPack a b 0 0 = (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) := by
  unfold TomlPack
  have hz1 : ((0 : UInt8).toUInt32 <<< 8) = 0 := rfl
  have hz2 : (0 : UInt8).toUInt32 = 0 := rfl
  rw [hz1, hz2, UInt32.or_zero, UInt32.or_zero]

theorem TomlPackThree (a b c : UInt8) :
    TomlPack a b c 0 = ((a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16)) |||
      (c.toUInt32 <<< 8) := by
  unfold TomlPack
  have hz : (0 : UInt8).toUInt32 = 0 := rfl
  rw [hz, UInt32.or_zero, UInt32.or_assoc]

theorem TomlPackFour (a b c d : UInt8) :
    TomlPack a b c d = (((a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16)) |||
      (c.toUInt32 <<< 8)) ||| d.toUInt32 := by
  unfold TomlPack
  rw [UInt32.or_assoc, UInt32.or_assoc]

theorem TomlPackThreshold (a b c d : UInt8) (k : Nat) (hk : k < 256) :
    (TomlPack a b c d < UInt32.ofNat (k * 16777216) ↔ a.toNat < k) := by
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, TomlPackNat, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxRecDepth 100000 in
theorem TomlContinuation (b : UInt8) (hb : 128 ≤ b.toNat ∧ b.toNat < 192) :
    ((b &&& 0xc0) != 0x80) = false := by
  have key : ∀ n, n < 256 → 128 ≤ n ∧ n < 192 →
      (((UInt8.ofNat n) &&& 0xc0) != 0x80) = false := by decide
  have h := key b.toNat b.toNat_lt hb
  simpa only [UInt8.ofNat_toNat] using h

theorem TomlLeadBetween (a : UInt8) (ha : 192 ≤ a.toNat ∧ a.toNat < 248) :
    JuliaLean.base.strings.string.between (· ≤ ·) a 0x80 0xf7 = true := by
  simp only [JuliaLean.base.strings.string.between, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le]
  change 128 ≤ a.toNat ∧ a.toNat ≤ 247
  omega

theorem TomlIxLength (n : Nat) (hn : n < 2 ^ 62) :
    (JuliaLean.Strings.ix (n : Int)).val = (n : Int) := by
  change wrapInt .i64 (n : Int) = (n : Int)
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem TomlIterStart (a : UInt8) (rest : Bytes) (hlen : (a :: rest).length < 2 ^ 62) :
    iterateStr (a :: rest) (i64 1) =
      if !(JuliaLean.base.strings.string.between (· ≤ ·) a 0x80 0xf7) then
        some (a.toUInt32 <<< 24, i64 2)
      else some (JuliaLean.base.strings.string.iterateContinued
        (fun s : Bytes => JuliaLean.Strings.ix s.length)
        (fun s i => s.getD (i.val.toNat - 1) 0) (a :: rest) (i64 1)
        (a.toUInt32 <<< 24)) := by
  have hn := TomlIxLength (a :: rest).length hlen
  have hg : decide ((JInt.rem .u64 (i64 1) - JInt.lit .u64 1).val <
      (JuliaLean.Strings.ix ((a :: rest).length : Int)).val) = true := by
    rw [hn]
    change decide ((0 : Int) < ((a :: rest).length : Int)) = true
    apply decide_eq_true
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  simp only [iterateStr, JuliaLean.base.strings.string.iterateString, hg,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem TomlIterOne (a : UInt8) (rest : Bytes) (ha : a.toNat < 128)
    (hlen : (a :: rest).length < 2 ^ 62) :
    iterateStr (a :: rest) (i64 1) = some (TomlPack a 0 0 0, i64 2) := by
  rw [TomlIterStart a rest hlen]
  have hb : JuliaLean.base.strings.string.between (· ≤ ·) a 0x80 0xf7 = false := by
    simp only [JuliaLean.base.strings.string.between, UInt8.le_iff_toNat_le]
    have hl : ¬ (0x80 : UInt8).toNat ≤ a.toNat := by change ¬128 ≤ a.toNat; omega
    simp only [hl, decide_false, Bool.false_and]
  rw [hb]
  simp only [Bool.not_false, ↓reduceIte, TomlPackOne]


theorem TomlIterTwo (a b : UInt8) (rest : Bytes)
    (ha : 192 ≤ a.toNat ∧ a.toNat < 224)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hlen : (a :: b :: rest).length < 2 ^ 62) :
    iterateStr (a :: b :: rest) (i64 1) = some (TomlPack a b 0 0, i64 3) := by
  have hn := TomlIxLength (a :: b :: rest).length hlen
  have hn1 : ¬ (i64 2).val > (JuliaLean.Strings.ix ((a :: b :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (2 : Int) > ((a :: b :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have nx1 : i64 1 + JuliaLean.Strings.ix 1 = i64 2 := rfl
  have nx2 : i64 2 + JuliaLean.Strings.ix 1 = i64 3 := rfl
  have r1 : (a :: b :: rest).getD ((i64 2).val.toNat - 1) 0 = b := rfl
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [← TomlPackOne]
    exact (not_congr (TomlPackThreshold a 0 0 0 192 (by decide))).mpr (by omega)
  have hc1 : (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [← TomlPackTwo]
    exact (TomlPackThreshold a b 0 0 224 (by decide)).mpr ha.2
  rw [TomlIterStart a (b :: rest) hlen, TomlLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [JuliaLean.base.strings.string.iterateContinued, Id.run, pure, hc0,
    ↓reduceIte, nx1, hn1, r1, TomlContinuation b hb, Bool.false_eq_true,
    nx2, hc1, decide_true, Bool.or_true]
  rw [TomlPackTwo]

theorem TomlIterThree (a b c : UInt8) (rest : Bytes)
    (ha : 224 ≤ a.toNat ∧ a.toNat < 240)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hlen : (a :: b :: c :: rest).length < 2 ^ 62) :
    iterateStr (a :: b :: c :: rest) (i64 1) = some (TomlPack a b c 0, i64 4) := by
  have hn := TomlIxLength (a :: b :: c :: rest).length hlen
  have hn1 : ¬ (i64 2).val > (JuliaLean.Strings.ix ((a :: b :: c :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (2 : Int) > ((a :: b :: c :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have hn2 : ¬ (i64 3).val > (JuliaLean.Strings.ix ((a :: b :: c :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (3 : Int) > ((a :: b :: c :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have nx1 : i64 1 + JuliaLean.Strings.ix 1 = i64 2 := rfl
  have nx2 : i64 2 + JuliaLean.Strings.ix 1 = i64 3 := rfl
  have nx3 : i64 3 + JuliaLean.Strings.ix 1 = i64 4 := rfl
  have r1 : (a :: b :: c :: rest).getD ((i64 2).val.toNat - 1) 0 = b := rfl
  have r2 : (a :: b :: c :: rest).getD ((i64 3).val.toNat - 1) 0 = c := rfl
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [← TomlPackOne]
    exact (not_congr (TomlPackThreshold a 0 0 0 192 (by decide))).mpr (by omega)
  have hc1 : ¬ (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [← TomlPackTwo]
    exact (not_congr (TomlPackThreshold a b 0 0 224 (by decide))).mpr (by omega)
  have hc2 : ((a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) ||| (c.toUInt32 <<< 8)) < 0xf0000000 := by
    rw [← TomlPackThree]
    exact (TomlPackThreshold a b c 0 240 (by decide)).mpr ha.2
  rw [TomlIterStart a (b :: c :: rest) hlen, TomlLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [JuliaLean.base.strings.string.iterateContinued, Id.run, pure, hc0,
    ↓reduceIte, nx1, hn1, r1, TomlContinuation b hb, Bool.false_eq_true,
    nx2, hc1, decide_false, Bool.or_false, nx3, hn2, r2, TomlContinuation c hc,
    hc2, decide_true, Bool.or_true]
  rw [TomlPackThree]

theorem TomlIterFour (a b c d : UInt8) (rest : Bytes)
    (ha : 240 ≤ a.toNat ∧ a.toNat < 248)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hd : 128 ≤ d.toNat ∧ d.toNat < 192)
    (hlen : (a :: b :: c :: d :: rest).length < 2 ^ 62) :
    iterateStr (a :: b :: c :: d :: rest) (i64 1) = some (TomlPack a b c d, i64 5) := by
  have hn := TomlIxLength (a :: b :: c :: d :: rest).length hlen
  have hn1 : ¬ (i64 2).val > (JuliaLean.Strings.ix ((a :: b :: c :: d :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (2 : Int) > ((a :: b :: c :: d :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have hn2 : ¬ (i64 3).val > (JuliaLean.Strings.ix ((a :: b :: c :: d :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (3 : Int) > ((a :: b :: c :: d :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have hn3 : ¬ (i64 4).val > (JuliaLean.Strings.ix ((a :: b :: c :: d :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (4 : Int) > ((a :: b :: c :: d :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have nx1 : i64 1 + JuliaLean.Strings.ix 1 = i64 2 := rfl
  have nx2 : i64 2 + JuliaLean.Strings.ix 1 = i64 3 := rfl
  have nx3 : i64 3 + JuliaLean.Strings.ix 1 = i64 4 := rfl
  have nx4 : i64 4 + JuliaLean.Strings.ix 1 = i64 5 := rfl
  have r1 : (a :: b :: c :: d :: rest).getD ((i64 2).val.toNat - 1) 0 = b := rfl
  have r2 : (a :: b :: c :: d :: rest).getD ((i64 3).val.toNat - 1) 0 = c := rfl
  have r3 : (a :: b :: c :: d :: rest).getD ((i64 4).val.toNat - 1) 0 = d := rfl
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [← TomlPackOne]
    exact (not_congr (TomlPackThreshold a 0 0 0 192 (by decide))).mpr (by omega)
  have hc1 : ¬ (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [← TomlPackTwo]
    exact (not_congr (TomlPackThreshold a b 0 0 224 (by decide))).mpr (by omega)
  have hc2 : ¬ ((a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) ||| (c.toUInt32 <<< 8)) < 0xf0000000 := by
    rw [← TomlPackThree]
    exact (not_congr (TomlPackThreshold a b c 0 240 (by decide))).mpr (by omega)
  rw [TomlIterStart a (b :: c :: d :: rest) hlen, TomlLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [JuliaLean.base.strings.string.iterateContinued, Id.run, pure, hc0,
    ↓reduceIte, nx1, hn1, r1, TomlContinuation b hb, Bool.false_eq_true,
    nx2, hc1, decide_false, Bool.or_false, nx3, hn2, r2, TomlContinuation c hc,
    hc2, nx4, hn3, r3, TomlContinuation d hd]
  rw [TomlPackFour]


/-- The first model iterator step decodes the complete leading Unicode scalar. -/
theorem TomlIterLiteralHead (c : Char) (suffix : String)
    (hsize : (String.singleton c ++ suffix).utf8ByteSize < 2 ^ 62) :
    ∃ pos, iterateStr (lit (String.singleton c ++ suffix)) (i64 1) = some (jc c, pos) := by
  have hlen : (lit (String.singleton c ++ suffix)).length < 2 ^ 62 := by
    rw [TomlLitLength]
    exact hsize
  rw [TomlLitAppend, TomlLitSingleton] at hlen ⊢
  by_cases hone : c.val.toNat ≤ 127
  · have he : String.utf8EncodeChar c = [TomlByte c.val.toNat] := by
      simp only [String.utf8EncodeChar, hone, ↓reduceIte, TomlByte]
    rw [he] at hlen ⊢
    rw [TomlJcOne c _ he]
    exact ⟨i64 2, TomlIterOne _ (lit suffix)
      (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩
  · by_cases htwo : c.val.toNat ≤ 2047
    · have he : String.utf8EncodeChar c =
          [TomlByte (c.val.toNat / 64 % 32 + 192), TomlByte (c.val.toNat % 64 + 128)] := by
        simp only [String.utf8EncodeChar, hone, htwo, ↓reduceIte, TomlByte]
      rw [he] at hlen ⊢
      rw [TomlJcTwo c _ _ he]
      exact ⟨i64 3, TomlIterTwo _ _ (lit suffix)
        (by rw [TomlByteNat _ (by omega)]; omega)
        (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩
    · by_cases hthree : c.val.toNat ≤ 65535
      · have he : String.utf8EncodeChar c =
            [TomlByte (c.val.toNat / 4096 % 16 + 224), TomlByte (c.val.toNat / 64 % 64 + 128),
              TomlByte (c.val.toNat % 64 + 128)] := by
          simp only [String.utf8EncodeChar, hone, htwo, hthree, ↓reduceIte, TomlByte]
        rw [he] at hlen ⊢
        rw [TomlJcThree c _ _ _ he]
        exact ⟨i64 4, TomlIterThree _ _ _ (lit suffix)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩
      · have he : String.utf8EncodeChar c =
            [TomlByte (c.val.toNat / 262144 % 8 + 240), TomlByte (c.val.toNat / 4096 % 64 + 128),
              TomlByte (c.val.toNat / 64 % 64 + 128), TomlByte (c.val.toNat % 64 + 128)] := by
          simp only [String.utf8EncodeChar, hone, htwo, hthree, ↓reduceIte, TomlByte]
        rw [he] at hlen ⊢
        rw [TomlJcFour c _ _ _ _ he]
        exact ⟨i64 5, TomlIterFour _ _ _ _ (lit suffix)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩

/-- Constructor initialization preserves the decoded leading character and disables comments. -/
theorem TomlNewHead {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)
    (c : Char) (suffix : String) (p : Parser X D CI CF)
    (hsize : (String.singleton c ++ suffix).utf8ByteSize < 2 ^ 62)
    (hnew : Parser_new o (lit (String.singleton c ++ suffix)) = some (.ok (.ok (), p))) :
    p.comments = none ∧ p.current_char = jc c := by
  obtain ⟨pos, hit⟩ := TomlIterLiteralHead c suffix hsize
  rw [ws_new_after] at hnew
  have hp : wsAfter (ib_initialParser o (lit (String.singleton c ++ suffix))) = p :=
    (Prod.mk.inj (Except.ok.inj (Option.some.inj hnew))).2
  rw [← hp]
  refine ⟨ws_after_comments _, ?_⟩
  unfold wsAfter
  change (wsAfterWith (ib_initialParser o (lit (String.singleton c ++ suffix)))
    (iterateStr (lit (String.singleton c ++ suffix)) (i64 1))).current_char = jc c
  rw [hit]
  cases hn : (jc c == jc '\n') <;>
    simp only [wsAfterWith, hn, Bool.false_eq_true, ↓reduceIte]

theorem TomlJcNeAscii (c d : Char) (hd : d.val.toNat ≤ 127) (hne : c ≠ d) :
    (jc c == jc d) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  exact hne (TomlJcAsciiInjective c d hd h)


section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)

/-- Non-whitespace, non-comment initial lookahead leaves the top-level skip unchanged. -/
theorem TomlSkipInitial (p : Parser X D CI CF)
    (hcomments : p.comments = none)
    (heof : (p.current_char == EOF_CHAR) = false)
    (hspace : iswhitespace p.current_char = false)
    (hnewline : isnewline p.current_char = false)
    (hhash : (p.current_char == jc '#') = false) :
    runP o (skip_ws_nl_toplevel o) p = some (.ok (.ok false, p)) := by
  have hw : runP o (accept_batch o (.fn fun x => iswhitespace x || isnewline x)) p =
      some (.ok (.ok false, p)) :=
    el_batch_stops o p _ (el_accept_stops o p _ heof
      (by change (iswhitespace p.current_char || isnewline p.current_char) = false
          rw [hspace, hnewline]; rfl))
  have hc : runP o (skip_comment o) p = some (.ok (.ok false, p)) :=
    el_comment_stops o p (el_accept_stops o p (chr '#') heof hhash)
  unfold skip_ws_nl_toplevel
  rw [el_bind_run, el_get_run]
  simp only [hcomments, Option.isNone_none, ↓reduceIte]
  exact el_ws_nl_stops o p false hw hc


/-- Initial key errors pass through the public driver with diagnostic fields attached. -/
theorem TomlTryparseInitialError (p q : Parser X D CI CF) (err : ParserError)
    (hcomments : p.comments = none)
    (heof : (p.current_char == EOF_CHAR) = false)
    (hspace : iswhitespace p.current_char = false)
    (hnewline : isnewline p.current_char = false)
    (hhash : (p.current_char == jc '#') = false)
    (hbracket : (p.current_char == jc '[') = false)
    (hkey : runP o (parse_key o) p = some (.ok (.error err, q))) :
    runP o (tryparse o) p = some (.ok (.error (el_decorateError q err), q)) := by
  apply el_tryparse_error_from_toplevel o p q false err
  · exact TomlSkipInitial o p hcomments heof hspace hnewline hhash
  · exact heof
  · exact el_toplevel_error_from_key o p q err
      (el_accept_stops o p (chr '[') heof hbracket) hkey

end

section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)

/-- The continuation reached only after a complete key has been parsed. -/
def TomlKeyTail (keyval : Bytes) : PM o (List Bytes) := do
  modifyP o fun l => { l with dotted_keys := l.dotted_keys ++ [keyval] }
  discard (skip_ws o)
  if (← accept o (chr '.')) then
    discard (skip_ws o)
    let _ ← _parse_key o
    pure ()
  return (← getP o).dotted_keys

/-- Bare-key parsing with the subsequent successful-key computation left abstract. -/
def TomlBareKeyThen {α : Type} (finish : Bytes → PM o α) : PM o α := do
  set_marker o
  if (← accept_batch o (.fn isvalid_barekey_char)) then
    let p ← peek o
    if !(p == jc '.' || iswhitespace p || p == jc ']' || p == jc '=') then
      let c ← eat_char o
      throwP o (ParserError_2 .ErrInvalidBareKeyCharacter (some c))
    let keyval ← take_substring o
    finish keyval
  else
    let c ← eat_char o
    let keyval ← throwP o (ParserError_2 .ErrInvalidBareKeyCharacter (some c))
    finish keyval

/-- Quoted or bare key, retaining the same continuation as the original parser. -/
def TomlKeyThen {α : Type} (finish : Bytes → PM o α) : PM o α := do
  if (← accept o (chr '"')) then
    let keyval ← parse_string_start o false (allow_multiline := false)
    finish keyval
  else
    if (← accept o (chr '\'')) then
      let keyval ← parse_string_start o true (allow_multiline := false)
      finish keyval
    else
      TomlBareKeyThen o finish

/-- One unfolding of the original parser, split at its semantic call boundaries. -/
theorem TomlKeyUnfold : _parse_key o = (do
    discard (skip_ws o)
    if (← getP o).dotted_keys.isEmpty then
      if (← accept o (chr '=')) then
        throwP o (ParserError_1 .ErrEmptyBareKey)
    TomlKeyThen o (TomlKeyTail o)) := by
  rw [_parse_key.eq_def]
  rfl

/-- Composition with an explicitly supplied successful action. -/
theorem TomlBindOk {α β : Type} (x : PM o α) (f : α → PM o β)
    (p q : Parser X D CI CF) (a : α)
    (result : Option (Except (Thrown E) (Err β × Parser X D CI CF)))
    (hx : runP o x p = some (.ok (.ok a, q)))
    (hf : runP o (f a) q = result) : runP o (x >>= f) p = result := by
  rw [el_bind_run, hx]
  exact hf

/-- Composition stops when its first action fails. -/
theorem TomlBindError {α β : Type} (x : PM o α) (f : α → PM o β)
    (p q : Parser X D CI CF) (err : ParserError)
    (hx : runP o x p = some (.ok (.error err, q))) :
    runP o (x >>= f) p = some (.ok (.error err, q)) := by
  rw [el_bind_run, hx]

/-- The bare-key failure path is independent of any successful-key continuation. -/
theorem TomlBareKeyThenError {α : Type} (finish : Bytes → PM o α)
    (p marked after : Parser X D CI CF) (c : JChar)
    (hm : runP o (set_marker o) p = some (.ok (.ok (), marked)))
    (hb : runP o (accept_batch o (.fn isvalid_barekey_char)) marked =
      some (.ok (.ok false, marked)))
    (he : runP o (eat_char o) marked = some (.ok (.ok c, after))) :
    runP o (TomlBareKeyThen o finish) p = some (.ok (.error
      (ParserError_2 .ErrInvalidBareKeyCharacter (some c)), after)) := by
  unfold TomlBareKeyThen
  apply TomlBindOk o (set_marker o) _ p marked () _ hm
  apply TomlBindOk o (accept_batch o (.fn isvalid_barekey_char)) _ marked marked false _ hb
  dsimp only
  apply TomlBindOk o (eat_char o) _ marked after c _ he
  exact TomlBindError o _ finish after after _ (el_throwP_run o _ after)

/-- Quote rejection preserves the subsequent bare-key failure. -/
theorem TomlKeyThenError {α : Type} (finish : Bytes → PM o α)
    (p marked after : Parser X D CI CF) (c : JChar)
    (hdq : runP o (accept o (chr '"')) p = some (.ok (.ok false, p)))
    (hsq : runP o (accept o (chr '\'')) p = some (.ok (.ok false, p)))
    (hm : runP o (set_marker o) p = some (.ok (.ok (), marked)))
    (hb : runP o (accept_batch o (.fn isvalid_barekey_char)) marked =
      some (.ok (.ok false, marked)))
    (he : runP o (eat_char o) marked = some (.ok (.ok c, after))) :
    runP o (TomlKeyThen o finish) p = some (.ok (.error
      (ParserError_2 .ErrInvalidBareKeyCharacter (some c)), after)) := by
  unfold TomlKeyThen
  simp only [el_bind_run, hdq, hsq, Bool.false_eq_true, ↓reduceIte]
  exact TomlBareKeyThenError o finish p marked after c hm hb he

/-- The initial whitespace/empty-key checks preserve a downstream key error. -/
theorem TomlKeyErrorFromChecks (p after : Parser X D CI CF) (err : ParserError)
    (hw : runP o (skip_ws o) p = some (.ok (.ok false, p)))
    (hk : p.dotted_keys.isEmpty = true)
    (heq : runP o (accept o (chr '=')) p = some (.ok (.ok false, p)))
    (hkey : runP o (TomlKeyThen o (TomlKeyTail o)) p = some (.ok (.error err, after))) :
    runP o (_parse_key o) p = some (.ok (.error err, after)) := by
  rw [TomlKeyUnfold]
  simp only [el_bind_run, el_discard_run, hw, el_get_run, hk, heq,
    Bool.false_eq_true, ↓reduceIte]
  exact hkey

/-- The empty-key check throws independently of all successful parsing continuations. -/
theorem TomlEmptyKeyFromChecks (p after : Parser X D CI CF)
    (hw : runP o (skip_ws o) p = some (.ok (.ok false, p)))
    (hk : p.dotted_keys.isEmpty = true)
    (heq : runP o (accept o (chr '=')) p = some (.ok (.ok true, after))) :
    runP o (_parse_key o) p = some (.ok (.error (ParserError_1 .ErrEmptyBareKey), after)) := by
  rw [TomlKeyUnfold]
  simp only [el_bind_run, el_discard_run, hw, el_get_run, hk, heq,
    el_throwP_run, ↓reduceIte]

/-- Parser state after clearing dotted keys and recording the key's start. -/
def TomlMarkedKey (p : Parser X D CI CF) : Parser X D CI CF :=
  { p with dotted_keys := [], marker := p.prevpos }

/-- An invalid bare-key character is rejected before any dictionary operations. -/
theorem TomlInvalidKeyError (p : Parser X D CI CF)
    (heof : (p.current_char == EOF_CHAR) = false)
    (hspace : iswhitespace p.current_char = false)
    (hequals : (p.current_char == jc '=') = false)
    (hdquote : (p.current_char == jc '"') = false)
    (hsquote : (p.current_char == jc '\'') = false)
    (hbare : isvalid_barekey_char p.current_char = false) :
    runP o (parse_key o) p = some (.ok (.error
      (ParserError_2 .ErrInvalidBareKeyCharacter (some p.current_char)),
      wsAfter (TomlMarkedKey p))) := by
  let q : Parser X D CI CF := { p with dotted_keys := [] }
  let marked := TomlMarkedKey p
  have hw : runP o (skip_ws o) q = some (.ok (.ok false, q)) :=
    el_batch_stops o q _ (el_accept_stops o q _ heof hspace)
  have heq : runP o (accept o (chr '=')) q = some (.ok (.ok false, q)) :=
    el_accept_stops o q _ heof hequals
  have hdq : runP o (accept o (chr '"')) q = some (.ok (.ok false, q)) :=
    el_accept_stops o q _ heof hdquote
  have hsq : runP o (accept o (chr '\'')) q = some (.ok (.ok false, q)) :=
    el_accept_stops o q _ heof hsquote
  have hm : runP o (set_marker o) q = some (.ok (.ok (), marked)) := rfl
  have hb : runP o (accept_batch o (.fn isvalid_barekey_char)) marked =
      some (.ok (.ok false, marked)) :=
    el_batch_stops o _ _ (el_accept_stops o _ _ heof hbare)
  have he : runP o (eat_char o) marked =
      some (.ok (.ok p.current_char, wsAfter marked)) := ws_eat_run o marked
  unfold parse_key
  apply TomlBindOk o (modifyP o fun l => {l with dotted_keys := []}) _ p q () _
    (el_modify_run o _ p)
  apply TomlKeyErrorFromChecks o q (wsAfter marked) _ hw rfl heq
  exact TomlKeyThenError o (TomlKeyTail o) q marked (wsAfter marked) p.current_char
    hdq hsq hm hb he

/-- The equals sign is accepted and immediately rejected as an empty bare key. -/
theorem TomlEmptyKeyError (p : Parser X D CI CF)
    (heq : p.current_char = jc '=') :
    runP o (parse_key o) p = some (.ok (.error (ParserError_1 .ErrEmptyBareKey),
      wsAfter { p with dotted_keys := [] })) := by
  let q : Parser X D CI CF := { p with dotted_keys := [] }
  have heof : (q.current_char == EOF_CHAR) = false := by
    change (p.current_char == EOF_CHAR) = false
    rw [heq, cc_jc_equals, cc_eof]
    decide
  have hspace : iswhitespace q.current_char = false := by
    change iswhitespace p.current_char = false
    rw [heq]
    simp only [iswhitespace, cc_jc_equals, cc_jc_space, cc_jc_tab]
    decide
  have hw : runP o (skip_ws o) q = some (.ok (.ok false, q)) :=
    el_batch_stops o q _ (el_accept_stops o q _ heof hspace)
  have ha : runP o (accept o (chr '=')) q = some (.ok (.ok true, wsAfter q)) :=
    wr_accept_yes o (chr '=') q (wsAfter q) q.current_char heof
      (by change (p.current_char == jc '=') = true; rw [heq]; exact BEq.rfl)
      (ws_eat_run o q)
  unfold parse_key
  apply TomlBindOk o (modifyP o fun l => {l with dotted_keys := []}) _ p q () _
    (el_modify_run o _ p)
  exact TomlEmptyKeyFromChecks o q (wsAfter q) hw rfl ha

end

section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)

/-- The parser driver preserves the invalid-bare-key error type. -/
theorem TomlInvalidInitialError (p : Parser X D CI CF)
    (hcomments : p.comments = none)
    (heof : (p.current_char == EOF_CHAR) = false)
    (hspace : iswhitespace p.current_char = false)
    (hnewline : isnewline p.current_char = false)
    (hhash : (p.current_char == jc '#') = false)
    (hbracket : (p.current_char == jc '[') = false)
    (hequals : (p.current_char == jc '=') = false)
    (hdquote : (p.current_char == jc '"') = false)
    (hsquote : (p.current_char == jc '\'') = false)
    (hbare : isvalid_barekey_char p.current_char = false) :
    ∃ after err, runP o (tryparse o) p = some (.ok (.error err, after)) ∧
      err.type = .ErrInvalidBareKeyCharacter := by
  let q := wsAfter (TomlMarkedKey p)
  let err := ParserError_2 .ErrInvalidBareKeyCharacter (some p.current_char)
  refine ⟨q, el_decorateError q err, ?_, rfl⟩
  apply el_tryparse_error_from_toplevel o p q false err
  · exact TomlSkipInitial o p hcomments heof hspace hnewline hhash
  · exact heof
  · apply el_toplevel_error_from_key o p q err
    · exact el_accept_stops o p (chr '[') heof hbracket
    · exact TomlInvalidKeyError o p heof hspace hequals hdquote hsquote hbare

/-- Initialized parsers at an equals sign return the empty-bare-key error. -/
theorem TomlEmptyInitialError (p : Parser X D CI CF)
    (hcomments : p.comments = none)
    (heq : p.current_char = jc '=') :
    ∃ after err, runP o (tryparse o) p = some (.ok (.error err, after)) := by
  have heof : (p.current_char == EOF_CHAR) = false := by
    rw [heq, cc_jc_equals, cc_eof]; decide
  have hspace : iswhitespace p.current_char = false := by
    rw [heq]; simp only [iswhitespace, cc_jc_equals, cc_jc_space, cc_jc_tab]; decide
  have hnewline : isnewline p.current_char = false := by
    rw [heq]; simp only [isnewline, cc_jc_equals, cc_jc_lf, cc_jc_cr]; decide
  have hhash : (p.current_char == jc '#') = false := by
    rw [heq, cc_jc_equals, cc_jc_hash]; decide
  have hbracket : (p.current_char == jc '[') = false := by
    rw [heq, cc_jc_equals, cc_jc_bracket]; decide
  let q := wsAfter { p with dotted_keys := [] }
  let err := ParserError_1 .ErrEmptyBareKey
  refine ⟨q, el_decorateError q err, ?_⟩
  apply el_tryparse_error_from_toplevel o p q false err
  · exact TomlSkipInitial o p hcomments heof hspace hnewline hhash
  · exact heof
  · apply el_toplevel_error_from_key o p q err
    · exact el_accept_stops o p (chr '[') heof hbracket
    · exact TomlEmptyKeyError o p heq

end


/-- toml-r1-tryparse-invalid-barekey: the initialized parser rejects any invalid initial scalar. -/
theorem TomlR1TryparseInvalidBarekey_proven :
    JuliaLean.Proofs.base.toml.parser.Round4.TryparseInvalidInitialBareKey := by
  intro X Y E D CI CF o c suffix p hbare hdquote hsquote hequals hbracket hhash _hbom
    hspace hnewline hsize hnew
  obtain ⟨hcomments, hchar⟩ := TomlNewHead o c suffix p hsize hnew
  apply TomlInvalidInitialError o p hcomments
  · rw [hchar]
    exact beq_eq_false_iff_ne.mpr (TomlJcNeEof c)
  · rw [hchar]; exact hspace
  · rw [hchar]; exact hnewline
  · rw [hchar]; exact TomlJcNeAscii c '#' (by decide) hhash
  · rw [hchar]; exact TomlJcNeAscii c '[' (by decide) hbracket
  · rw [hchar]; exact TomlJcNeAscii c '=' (by decide) hequals
  · rw [hchar]; exact TomlJcNeAscii c '"' (by decide) hdquote
  · rw [hchar]; exact TomlJcNeAscii c '\'' (by decide) hsquote
  · rw [hchar]; exact hbare



/-- toml-r1-parse-invalid-barekey: parse throws the error returned by tryparse. -/
theorem TomlR1ParseInvalidBarekey_proven :
    JuliaLean.Proofs.base.toml.parser.Round4.ParseInvalidInitialBareKey := by
  intro X Y E D CI CF o c suffix p hbare hdquote hsquote hequals hbracket hhash hbom
    hspace hnewline hsize hnew
  obtain ⟨after, err, hrun, htype⟩ := TomlR1TryparseInvalidBarekey_proven o c suffix p
    hbare hdquote hsquote hequals hbracket hhash hbom hspace hnewline hsize hnew
  exact ⟨err, el_parse_error_of_tryparse o p after err hrun, htype⟩



/-- toml-r1-tryparse-empty-barekey: a leading equals sign is rejected as an empty key. -/
theorem TomlR1TryparseEmptyBarekey_proven :
    JuliaLean.Proofs.base.toml.parser.Round4.TryparseEmptyBareKey := by
  intro X Y E D CI CF o suffix p hsize hnew
  have hs : String.singleton '=' = "=" := rfl
  have hsize' : (String.singleton '=' ++ suffix).utf8ByteSize < 2 ^ 62 := by
    rw [hs]; exact hsize
  have hnew' : Parser_new o (lit (String.singleton '=' ++ suffix)) =
      some (.ok (.ok (), p)) := by rw [hs]; exact hnew
  obtain ⟨hcomments, hchar⟩ := TomlNewHead o '=' suffix p hsize' hnew'
  exact TomlEmptyInitialError o p hcomments hchar



/-- toml-r1-parse-empty-barekey: parse propagates the concrete empty-key parser error. -/
theorem TomlR1ParseEmptyBarekey_proven :
    JuliaLean.Proofs.base.toml.parser.Round4.ParseEmptyBareKey := by
  intro X Y E D CI CF o suffix p hsize hnew
  obtain ⟨after, err, hrun⟩ := TomlR1TryparseEmptyBarekey_proven o suffix p hsize hnew
  exact ⟨err, el_parse_error_of_tryparse o p after err hrun⟩

end JuliaLean.ChatGPT.Batch3.Group4
namespace JuliaLean.Proofs.base.toml.parser
open JuliaLean.Registry

end JuliaLean.Proofs.base.toml.parser

namespace JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean JuliaLean.base.toml.parser
open JuliaLean.Proofs.base.toml.parser
open JuliaLean.Proofs.base.toml.parser.JuliaLean.ChatGPT.Batch2.Group1
open JuliaLean.ChatGPT.Batch3.Group4

set_option maxRecDepth 8192

section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)


end

theorem g17TomlIterStart3 (a : UInt8) (rest : Bytes) (hlen : (34 :: 92 :: a :: rest).length < 2 ^ 62) :
    iterateStr (34 :: 92 :: a :: rest) (i64 3) =
      if !(JuliaLean.base.strings.string.between (· ≤ ·) a 0x80 0xf7) then
        some (a.toUInt32 <<< 24, i64 4)
      else some (JuliaLean.base.strings.string.iterateContinued
        (fun s : Bytes => JuliaLean.Strings.ix s.length)
        (fun s i => s.getD (i.val.toNat - 1) 0) (34 :: 92 :: a :: rest) (i64 3)
        (a.toUInt32 <<< 24)) := by
  have hn := TomlIxLength (34 :: 92 :: a :: rest).length hlen
  have hg : decide ((JInt.rem .u64 (i64 3) - JInt.lit .u64 1).val <
      (JuliaLean.Strings.ix ((34 :: 92 :: a :: rest).length : Int)).val) = true := by
    rw [hn]
    change decide ((2 : Int) < ((34 :: 92 :: a :: rest).length : Int)) = true
    apply decide_eq_true
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  simp only [iterateStr, JuliaLean.base.strings.string.iterateString, hg,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem g17TomlIterOne3 (a : UInt8) (rest : Bytes) (ha : a.toNat < 128)
    (hlen : (34 :: 92 :: a :: rest).length < 2 ^ 62) :
    iterateStr (34 :: 92 :: a :: rest) (i64 3) = some (TomlPack a 0 0 0, i64 4) := by
  rw [g17TomlIterStart3 a rest hlen]
  have hb : JuliaLean.base.strings.string.between (· ≤ ·) a 0x80 0xf7 = false := by
    simp only [JuliaLean.base.strings.string.between, UInt8.le_iff_toNat_le]
    have hl : ¬ (0x80 : UInt8).toNat ≤ a.toNat := by change ¬128 ≤ a.toNat; omega
    simp only [hl, decide_false, Bool.false_and]
  rw [hb]
  simp only [Bool.not_false, ↓reduceIte, TomlPackOne]

theorem g17TomlIterTwo3 (a b : UInt8) (rest : Bytes)
    (ha : 192 ≤ a.toNat ∧ a.toNat < 224)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hlen : (34 :: 92 :: a :: b :: rest).length < 2 ^ 62) :
    iterateStr (34 :: 92 :: a :: b :: rest) (i64 3) = some (TomlPack a b 0 0, i64 5) := by
  have hn := TomlIxLength (34 :: 92 :: a :: b :: rest).length hlen
  have hn1 : ¬ (i64 4).val > (JuliaLean.Strings.ix ((34 :: 92 :: a :: b :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (4 : Int) > ((34 :: 92 :: a :: b :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have nx1 : i64 3 + JuliaLean.Strings.ix 1 = i64 4 := rfl
  have nx2 : i64 4 + JuliaLean.Strings.ix 1 = i64 5 := rfl
  have r1 : (34 :: 92 :: a :: b :: rest).getD ((i64 4).val.toNat - 1) 0 = b := rfl
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [← TomlPackOne]
    exact (not_congr (TomlPackThreshold a 0 0 0 192 (by decide))).mpr (by omega)
  have hc1 : (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [← TomlPackTwo]
    exact (TomlPackThreshold a b 0 0 224 (by decide)).mpr ha.2
  rw [g17TomlIterStart3 a (b :: rest) hlen, TomlLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [JuliaLean.base.strings.string.iterateContinued, Id.run, pure, hc0,
    ↓reduceIte, nx1, hn1, r1, TomlContinuation b hb, Bool.false_eq_true,
    nx2, hc1, decide_true, Bool.or_true]
  rw [TomlPackTwo]

theorem g17TomlIterThree3 (a b c : UInt8) (rest : Bytes)
    (ha : 224 ≤ a.toNat ∧ a.toNat < 240)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hlen : (34 :: 92 :: a :: b :: c :: rest).length < 2 ^ 62) :
    iterateStr (34 :: 92 :: a :: b :: c :: rest) (i64 3) = some (TomlPack a b c 0, i64 6) := by
  have hn := TomlIxLength (34 :: 92 :: a :: b :: c :: rest).length hlen
  have hn1 : ¬ (i64 4).val > (JuliaLean.Strings.ix ((34 :: 92 :: a :: b :: c :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (4 : Int) > ((34 :: 92 :: a :: b :: c :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have hn2 : ¬ (i64 5).val > (JuliaLean.Strings.ix ((34 :: 92 :: a :: b :: c :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (5 : Int) > ((34 :: 92 :: a :: b :: c :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have nx1 : i64 3 + JuliaLean.Strings.ix 1 = i64 4 := rfl
  have nx2 : i64 4 + JuliaLean.Strings.ix 1 = i64 5 := rfl
  have nx3 : i64 5 + JuliaLean.Strings.ix 1 = i64 6 := rfl
  have r1 : (34 :: 92 :: a :: b :: c :: rest).getD ((i64 4).val.toNat - 1) 0 = b := rfl
  have r2 : (34 :: 92 :: a :: b :: c :: rest).getD ((i64 5).val.toNat - 1) 0 = c := rfl
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [← TomlPackOne]
    exact (not_congr (TomlPackThreshold a 0 0 0 192 (by decide))).mpr (by omega)
  have hc1 : ¬ (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [← TomlPackTwo]
    exact (not_congr (TomlPackThreshold a b 0 0 224 (by decide))).mpr (by omega)
  have hc2 : ((a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) ||| (c.toUInt32 <<< 8)) < 0xf0000000 := by
    rw [← TomlPackThree]
    exact (TomlPackThreshold a b c 0 240 (by decide)).mpr ha.2
  rw [g17TomlIterStart3 a (b :: c :: rest) hlen, TomlLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [JuliaLean.base.strings.string.iterateContinued, Id.run, pure, hc0,
    ↓reduceIte, nx1, hn1, r1, TomlContinuation b hb, Bool.false_eq_true,
    nx2, hc1, decide_false, Bool.or_false, nx3, hn2, r2, TomlContinuation c hc,
    hc2, decide_true, Bool.or_true]
  rw [TomlPackThree]

theorem g17TomlIterFour3 (a b c d : UInt8) (rest : Bytes)
    (ha : 240 ≤ a.toNat ∧ a.toNat < 248)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hd : 128 ≤ d.toNat ∧ d.toNat < 192)
    (hlen : (34 :: 92 :: a :: b :: c :: d :: rest).length < 2 ^ 62) :
    iterateStr (34 :: 92 :: a :: b :: c :: d :: rest) (i64 3) = some (TomlPack a b c d, i64 7) := by
  have hn := TomlIxLength (34 :: 92 :: a :: b :: c :: d :: rest).length hlen
  have hn1 : ¬ (i64 4).val > (JuliaLean.Strings.ix ((34 :: 92 :: a :: b :: c :: d :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (4 : Int) > ((34 :: 92 :: a :: b :: c :: d :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have hn2 : ¬ (i64 5).val > (JuliaLean.Strings.ix ((34 :: 92 :: a :: b :: c :: d :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (5 : Int) > ((34 :: 92 :: a :: b :: c :: d :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have hn3 : ¬ (i64 6).val > (JuliaLean.Strings.ix ((34 :: 92 :: a :: b :: c :: d :: rest).length : Int)).val := by
    rw [hn]
    change ¬ (6 : Int) > ((34 :: 92 :: a :: b :: c :: d :: rest).length : Int)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega
  have nx1 : i64 3 + JuliaLean.Strings.ix 1 = i64 4 := rfl
  have nx2 : i64 4 + JuliaLean.Strings.ix 1 = i64 5 := rfl
  have nx3 : i64 5 + JuliaLean.Strings.ix 1 = i64 6 := rfl
  have nx4 : i64 6 + JuliaLean.Strings.ix 1 = i64 7 := rfl
  have r1 : (34 :: 92 :: a :: b :: c :: d :: rest).getD ((i64 4).val.toNat - 1) 0 = b := rfl
  have r2 : (34 :: 92 :: a :: b :: c :: d :: rest).getD ((i64 5).val.toNat - 1) 0 = c := rfl
  have r3 : (34 :: 92 :: a :: b :: c :: d :: rest).getD ((i64 6).val.toNat - 1) 0 = d := rfl
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [← TomlPackOne]
    exact (not_congr (TomlPackThreshold a 0 0 0 192 (by decide))).mpr (by omega)
  have hc1 : ¬ (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [← TomlPackTwo]
    exact (not_congr (TomlPackThreshold a b 0 0 224 (by decide))).mpr (by omega)
  have hc2 : ¬ ((a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) ||| (c.toUInt32 <<< 8)) < 0xf0000000 := by
    rw [← TomlPackThree]
    exact (not_congr (TomlPackThreshold a b c 0 240 (by decide))).mpr (by omega)
  rw [g17TomlIterStart3 a (b :: c :: d :: rest) hlen, TomlLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [JuliaLean.base.strings.string.iterateContinued, Id.run, pure, hc0,
    ↓reduceIte, nx1, hn1, r1, TomlContinuation b hb, Bool.false_eq_true,
    nx2, hc1, decide_false, Bool.or_false, nx3, hn2, r2, TomlContinuation c hc,
    hc2, nx4, hn3, r3, TomlContinuation d hd]
  rw [TomlPackFour]

/-- The first model iterator step decodes the complete leading Unicode scalar. -/
theorem g17TomlIterLiteralHead3 (c : Char) (suffix : String)
    (hsize : 2 + (String.singleton c ++ suffix).utf8ByteSize < 2 ^ 62) :
    ∃ pos, iterateStr (34 :: 92 :: lit (String.singleton c ++ suffix)) (i64 3) = some (jc c, pos) := by
  have hlen : (34 :: 92 :: lit (String.singleton c ++ suffix)).length < 2 ^ 62 := by
    simp only [List.length_cons, TomlLitLength]
    omega
  rw [TomlLitAppend, TomlLitSingleton] at hlen ⊢
  by_cases hone : c.val.toNat ≤ 127
  · have he : String.utf8EncodeChar c = [TomlByte c.val.toNat] := by
      simp only [String.utf8EncodeChar, hone, ↓reduceIte, TomlByte]
    rw [he] at hlen ⊢
    rw [TomlJcOne c _ he]
    exact ⟨i64 4, g17TomlIterOne3 _ (lit suffix)
      (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩
  · by_cases htwo : c.val.toNat ≤ 2047
    · have he : String.utf8EncodeChar c =
          [TomlByte (c.val.toNat / 64 % 32 + 192), TomlByte (c.val.toNat % 64 + 128)] := by
        simp only [String.utf8EncodeChar, hone, htwo, ↓reduceIte, TomlByte]
      rw [he] at hlen ⊢
      rw [TomlJcTwo c _ _ he]
      exact ⟨i64 5, g17TomlIterTwo3 _ _ (lit suffix)
        (by rw [TomlByteNat _ (by omega)]; omega)
        (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩
    · by_cases hthree : c.val.toNat ≤ 65535
      · have he : String.utf8EncodeChar c =
            [TomlByte (c.val.toNat / 4096 % 16 + 224), TomlByte (c.val.toNat / 64 % 64 + 128),
              TomlByte (c.val.toNat % 64 + 128)] := by
          simp only [String.utf8EncodeChar, hone, htwo, hthree, ↓reduceIte, TomlByte]
        rw [he] at hlen ⊢
        rw [TomlJcThree c _ _ _ he]
        exact ⟨i64 6, g17TomlIterThree3 _ _ _ (lit suffix)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩
      · have he : String.utf8EncodeChar c =
            [TomlByte (c.val.toNat / 262144 % 8 + 240), TomlByte (c.val.toNat / 4096 % 64 + 128),
              TomlByte (c.val.toNat / 64 % 64 + 128), TomlByte (c.val.toNat % 64 + 128)] := by
          simp only [String.utf8EncodeChar, hone, htwo, hthree, ↓reduceIte, TomlByte]
        rw [he] at hlen ⊢
        rw [TomlJcFour c _ _ _ _ he]
        exact ⟨i64 7, g17TomlIterFour3 _ _ _ _ (lit suffix)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega)
          (by rw [TomlByteNat _ (by omega)]; omega) hlen⟩


section
variable {X Y E D CI CF : Type} (o : Ops X Y E D CI CF)


theorem g17TomlQuotedKeyThenError {α : Type} (finish : Bytes → PM o α)
    (p q after : Parser X D CI CF) (err : ParserError)
    (ha : runP o (accept o (chr '"')) p = some (.ok (.ok true, q)))
    (hs : runP o (parse_string_start o false false) q = some (.ok (.error err, after))) :
    runP o (TomlKeyThen o finish) p = some (.ok (.error err, after)) := by
  unfold TomlKeyThen
  rw [el_bind_run, ha]
  exact TomlBindError o _ finish q after err hs


end

end JuliaLean.ChatGPT.Batch4.Group17

namespace JuliaLean.Proofs.base.toml.parser
open JuliaLean.Registry
open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-toml-lexer-char" "base/toml/parser.jl" ["next_char", "eat_char", "peek"]
    "TOML character movement preserves state and updates indices, lines and columns."
    "base/toml/parser.jl:413-433" ``TomlLex.NextCharSpec ``TomlLex.nextCharSpec,
  proven "docssyntaxcov-toml-lexer-accept" "base/toml/parser.jl" ["accept", "accept_batch", "accept_n"]
    "TOML acceptance consumes exactly the accepted lookahead run."
    "base/toml/parser.jl:437-467" ``TomlLex.AcceptBatchSpec ``TomlLex.acceptBatchSpec,
  proven "docssyntaxcov-toml-lexer-accept-one" "base/toml/parser.jl" ["accept"]
    "accept eats only an accepted non-EOF lookahead."
    "base/toml/parser.jl:437-448" ``TomlLex.AcceptSpec ``TomlLex.acceptSpec,
  proven "docssyntaxcov-toml-lexer-accept-n" "base/toml/parser.jl" ["accept_n"]
    "accept_n mirrors its recursive count."
    "base/toml/parser.jl:460-467" ``TomlLex.AcceptNSpec ``TomlLex.acceptNSpec,
  proven "docssyntaxcov-toml-whitespace" "base/toml/parser.jl"
    ["iswhitespace", "isnewline", "skip_ws", "skip_ws_nl_no_comment"]
    "Whitespace predicates and skippers stop on the first nonmatching lookahead."
    "base/toml/parser.jl:469-474" ``TomlLex.SkipWsSpec ``TomlLex.skipWsSpec,
  proven "docssyntaxcov-toml-comments" "base/toml/parser.jl"
    ["skip_comment", "skip_ws_nl", "skip_ws_nl_toplevel", "skip_ws_comment"]
    "Comment skipping consumes comments and queues captured text."
    "base/toml/parser.jl:476-544" ``TomlLex.SkipCommentSpec ``TomlLex.skipCommentSpec,
  proven "docssyntaxcov-toml-comment-state" "base/toml/parser.jl"
    ["flush_pending_comments!", "attach_pending_comments!", "attach_inline_comment!"]
    "Captured comments move to floating, above and inline containers."
    "base/toml/parser.jl:546-571" ``TomlLex.AttachSpec ``TomlLex.attachSpec,
  proven "docssyntaxcov-toml-path-marker" "base/toml/parser.jl"
    ["path_traverses_array", "set_marker!", "take_substring"]
    "Path traversal detects arrays and marker slicing uses the recorded prior position."
    "base/toml/parser.jl:573-585" ``TomlLex.PathTraversesArraySpec ``TomlLex.pathTraversesArraySpec,
  proven "docssyntaxcov-toml-containers" "base/toml/parser.jl"
    ["CommentBlock", "Comments", "isempty", "empty!", "=="]
    "Comment containers construct, clear and compare their fields."
    "base/toml/parser.jl:45-69" ``TomlLex.CommentContainers ``TomlLex.commentContainers,
  proven "docssyntaxcov-toml-parser-construction" "base/toml/parser.jl" ["Parser", "startup", "reinit!"]
    "Parser constructors and reinit establish the same fresh state."
    "base/toml/parser.jl:136-209" ``TomlLex.ParserConstruction ``TomlLex.parserConstruction,
  proven "docssyntaxcov-toml-try-macro" "base/toml/parser.jl" ["@try"]
    "@try returns ParserError values and otherwise yields the result."
    "base/toml/parser.jl:219-225" ``TomlLex.TryMacro ``TomlLex.tryMacroSpec,
  proven "docssyntaxcov-toml-errors" "base/toml/parser.jl"
    ["ParserError", "format_error_message_for_err_type", "point_to_line", "showerror"]
    "Parser errors construct and format their message, location and caret line."
    "base/toml/parser.jl:340-406" ``TomlLex.FormatErrorSpec ``TomlLex.formatErrorSpec,
  proven "docssyntaxcov-toml-datetime-copy" "base/toml/parser.jl" ["DateTime", "copyto_typed!"]
    "DateTime composes Date and Time and typed copying preserves length and prefix."
    "base/toml/parser.jl:23-24,879-884" ``TomlLex.CopytoTypedSpec ``TomlLex.copytoTypedSpec,
  proven "docssyntaxcov-toml-eat-char" "base/toml/parser.jl" ["eat_char"]
    "eat_char returns the lookahead and replaces it with next_char."
    "base/toml/parser.jl:427-431" ``TomlLex.EatCharSpec ``TomlLex.eatCharSpec,
  proven "docssyntaxcov-toml-peek" "base/toml/parser.jl" ["peek"]
    "peek returns the current lookahead without changing the parser."
    "base/toml/parser.jl:433" ``TomlLex.PeekSpec ``TomlLex.peekSpec,
  proven "docssyntaxcov-toml-whitespace-predicates" "base/toml/parser.jl" ["iswhitespace", "isnewline"]
    "TOML whitespace is space or tab and newline is LF or CR."
    "base/toml/parser.jl:469-470" ``TomlLex.WsNlSpec ``TomlLex.wsNlSpec,
  proven "docssyntaxcov-toml-skip-wsnl" "base/toml/parser.jl" ["skip_ws_nl"]
    "skip_ws_nl mirrors one whitespace and comment iteration before stopping or recurring."
    "base/toml/parser.jl:476-490" ``TomlLex.SkipWsNlSpec ``TomlLex.skipWsNlSpec,
  proven "docssyntaxcov-toml-skip-ws-comment" "base/toml/parser.jl" ["skip_ws_comment"]
    "skip_ws_comment runs skip_ws followed by skip_comment."
    "base/toml/parser.jl:541-544" ``TomlLex.SkipWsCommentSpec ``TomlLex.skipWsCommentSpec,
  proven "docssyntaxcov-toml-flush-comments" "base/toml/parser.jl" ["flush_pending_comments!"]
    "Flushing comments moves the pending queue to the active table and clears it."
    "base/toml/parser.jl:546-555" ``TomlLex.FlushSpec ``TomlLex.flushSpec,
  proven "docssyntaxcov-toml-toplevel-comments" "base/toml/parser.jl" ["skip_ws_nl_toplevel"]
    "Top-level whitespace skipping selects its capture or no-capture loop."
    "base/toml/parser.jl:493-524" ``TomlLex.ToplevelSpec ``TomlLex.toplevelSpec,
  proven "docssyntaxcov-toml-marker" "base/toml/parser.jl" ["set_marker!", "take_substring"]
    "The marker records prevpos and take_substring slices through the byte before lookahead."
    "base/toml/parser.jl:584-585" ``TomlLex.MarkerSpec ``TomlLex.markerSpec,
  proven "docssyntaxcov-toml-error-constructors" "base/toml/parser.jl" ["ParserError"]
    "ParserError constructors leave source locations unset."
    "base/toml/parser.jl:340-341" ``TomlLex.ParserErrorCtors ``TomlLex.parserErrorCtors,
  proven "docssyntaxcov-toml-point-line" "base/toml/parser.jl" ["point_to_line"]
    "point_to_line rejects reversed intervals and runs the caret-line traversal after index normalization."
    "base/toml/parser.jl:365-385" ``TomlLex.PointToLineSpec ``TomlLex.pointToLineSpec,
  proven "docssyntaxcov-toml-showerror" "base/toml/parser.jl" ["showerror"]
    "showerror composes the message, location, source line and marker line."
    "base/toml/parser.jl:387-406" ``TomlLex.ShowerrorSpec ``TomlLex.showerrorSpec,
  proven "docssyntaxcov-toml-datetime-constructor" "base/toml/parser.jl" ["DateTime"]
    "The seven-argument DateTime constructor composes Date and Time."
    "base/toml/parser.jl:23-24" ``TomlLex.DateTimeCtor ``TomlLex.dateTimeCtor,
  proven "docssyntaxcov-toml-value-methods" "base/toml/parser.jl"
    ["parse_toplevel", "parse_key", "parse_value", "parse_inline_table", "parse_inf", "parse_nan", "parse_bool", "isvalid_hex", "isvalid_oct", "isvalid_binary", "accept_batch_underscore", "take_string_or_substring", "parse_integer", "parse_hex", "parse_oct", "parse_bin", "ok_end_value"]
    "TOML value helpers terminate with a value or explicit exception, and character predicates match their bodies."
    "base/toml/parser.jl:620-642,807-1170" ``TomlRows.ValueMethodTotality ``TomlRows.valueMethodTotality,
  proven "docssyntaxcov-toml-date-methods" "base/toml/parser.jl"
    ["accept_two", "try_return_datetime", "try_return_date", "try_return_time", "_parse_local_time", "parse_local_time", "parse_datetime"]
    "TOML date and time helpers terminate with a value or explicit parser exception."
    "base/toml/parser.jl:1197-1353" ``TomlRows.DateMethodTotality ``TomlRows.dateMethodTotality,
  proven "docssyntaxcov-toml-string-methods" "base/toml/parser.jl"
    ["parse_string_start", "parse_string_continue", "take_chunks", "stop_candidates_multiline", "stop_candidates_singleline", "stop_candidates_multiline_quoted", "stop_candidates_singleline_quoted"]
    "TOML string helpers terminate with a string or explicit exception, and stop predicates match their delimiters."
    "base/toml/parser.jl:1360-1462" ``TomlRows.StringMethodTotality ``TomlRows.stringMethodTotality,

  { id := "toml-r1-tryparse-invalid-barekey"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["tryparse(l::Parser)@599"]
    statement := "A bounded, parser-initialized input with an invalid initial bare-key character makes tryparse return ErrInvalidBareKeyCharacter."
    source := "TOML 1.0 Keys, raw spec lines 102-109; base/toml/parser.jl:599-616; stdlib/TOML/docs/src/index.md:42-44; JuliaLean/base/toml/parser.lean:1045-1075,2722-2744,3325-3340"
    status := .proven
    prop := ``Round4.TryparseInvalidInitialBareKey
    thm := some ``JuliaLean.ChatGPT.Batch3.Group4.TomlR1TryparseInvalidBarekey_proven },
  { id := "toml-r1-parse-invalid-barekey"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["parse(l::Parser)@593"]
    statement := "A bounded, parser-initialized input with an invalid initial bare-key character makes parse throw ParserError caused by ErrInvalidBareKeyCharacter."
    source := "TOML 1.0 Keys, raw spec lines 102-109; base/toml/parser.jl:593-597,812-846; stdlib/TOML/src/TOML.jl:115-132; JuliaLean/base/toml/parser.lean:1045-1075,2722-2744,3387-3391"
    status := .proven
    prop := ``Round4.ParseInvalidInitialBareKey
    thm := some ``JuliaLean.ChatGPT.Batch3.Group4.TomlR1ParseInvalidBarekey_proven },
  { id := "toml-r1-tryparse-empty-barekey"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["tryparse(l::Parser)@599"]
    statement := "A bounded, parser-initialized input beginning with an empty bare key makes tryparse return ParserError."
    source := "TOML 1.0 Keys, raw lines 130-136; base/toml/parser.jl:599-616,812-818; stdlib/TOML/docs/src/index.md:42-44; JuliaLean/base/toml/parser.lean:1045-1075,2722-2727,3325-3340"
    status := .proven
    prop := ``Round4.TryparseEmptyBareKey
    thm := some ``JuliaLean.ChatGPT.Batch3.Group4.TomlR1TryparseEmptyBarekey_proven },
  { id := "toml-r1-parse-empty-barekey"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["parse(l::Parser)@593"]
    statement := "A bounded, parser-initialized input beginning with an empty bare key makes parse throw ParserError."
    source := "TOML 1.0 Keys, raw lines 130-136; base/toml/parser.jl:593-597,812-818; stdlib/TOML/src/TOML.jl:115-132; JuliaLean/base/toml/parser.lean:1045-1075,2722-2727,3387-3391"
    status := .proven
    prop := ``Round4.ParseEmptyBareKey
    thm := some ``JuliaLean.ChatGPT.Batch3.Group4.TomlR1ParseEmptyBarekey_proven },
  { id := "toml-r1-tryparse-error-location"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["tryparse(l::Parser)@599"]
    statement := "For every source beginning @, tryparse reports the original source at line 1, column 1."
    source := "TOML.tryparse diagnostic example, stdlib/TOML/docs/src/index.md:42-61; TOML 1.0 bare-key alphabet, raw lines 107-109; base/toml/parser.jl:599-616"
    status := .refuted
    prop := ``Round2.TryparseInvalidInitialBareKeyLocation
    thm := some ``JuliaLean.ChatGPT.Batch2.Group1.TomlR1TryparseErrorLocation_refuted,
    issue := "none found (queries: issues: TOML ParserError column -1; issues: TOML error location line column; issues: TOML parse error wrong line)" },
  { id := "toml-r1-parse-error-location"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["parse(l::Parser)@593"]
    statement := "For every source beginning @, parse throws ParserError with the original source at line 1, column 1."
    source := "TOML.parse docs, stdlib/TOML/src/TOML.jl:116-120; TOML 1.0 bare-key alphabet, raw lines 107-109; base/toml/parser.jl:593-616"
    status := .refuted
    prop := ``Round2.ParseInvalidInitialBareKeyLocation
    thm := some ``JuliaLean.ChatGPT.Batch2.Group1.TomlR1ParseErrorLocation_refuted,
    issue := "none found (queries: issues: TOML ParserError column -1; issues: TOML error location line column; issues: TOML parse error wrong line)" },
  { id := "toml-r1-tryparse-whitespace-root"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["tryparse(l::Parser)@599"]
    statement := "Every valid whitespace-only document using space, tab, LF, or CRLF returns its root table."
    source := "TOML.tryparse docs, stdlib/TOML/docs/src/index.md:42-44; TOML 1.0 Spec raw lines 45-46 and Table raw lines 746-748; base/toml/parser.jl:599-616"
    status := .proven
    prop := ``Round2.TryparseWhitespaceOnlyReturnsRoot
    thm := some ``JuliaLean.ChatGPT.Batch2.Group1.TomlR1TryparseWhitespaceRoot_proven },
  { id := "toml-r1-parse-whitespace-root"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["parse(l::Parser)@593"]
    statement := "The same valid whitespace-only documents return their root table."
    source := "TOML.parse docs, stdlib/TOML/src/TOML.jl:116-132; TOML 1.0 raw lines 45-46 and 746-748; base/toml/parser.jl:593-597"
    status := .proven
    prop := ``Round2.ParseWhitespaceOnlyReturnsRoot
    thm := some ``JuliaLean.ChatGPT.Batch2.Group1.TomlR1ParseWhitespaceRoot_proven },
  { id := "toml-r1-tryparse-invalid-escape"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["tryparse(l::Parser)@599"]
    statement := "An unrecognized non-newline escape in a basic quoted key returns ParserError."
    source := "TOML.tryparse docs, stdlib/TOML/docs/src/index.md:42-44; TOML 1.1 String, toml-lang/toml/1.1.0/toml.md:250-355; base/toml/parser.jl:1383-1446"
    status := .todo
    prop := ``Round5.TryparseInvalidNonnewlineEscapeInQuotedKey
    thm := none, notes := "The all-width UTF-8 invalid-escape parser-loop proof is incomplete." },
  { id := "toml-r1-parse-invalid-escape"
    juliaFile := "base/toml/parser.jl"
    juliaFns := ["parse(l::Parser)@593"]
    statement := "The same unrecognized non-newline escape inputs throw ParserError."
    source := "TOML.parse docs, stdlib/TOML/src/TOML.jl:116-120; TOML 1.1 String, toml-lang/toml/1.1.0/toml.md:250-355; base/toml/parser.jl:1383-1446"
    status := .todo
    prop := ``Round5.ParseInvalidNonnewlineEscapeInQuotedKey
    thm := none, notes := "The parse endpoint depends on the unproved all-width invalid-escape tryparse contract." }
]

end JuliaLean.Proofs.base.toml.parser
