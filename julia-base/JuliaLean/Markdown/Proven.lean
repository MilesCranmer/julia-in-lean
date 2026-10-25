import JuliaLean.Markdown.Props

/-!
# Markdown: proven properties

* `htmlescSound_proven`: `htmlesc` removes `<`, `>`, `"` and is undone by decoding its four
  entities.
* `htmlTagSafeTitles_proven`: in `html` output of any document without raw HTML whose
  admonition titles contain no `<`, every `<` starts one of the printer's own tags. Together
  with `htmlTextEscaped_refuted` this locates the only unescaped text: admonition titles.
-/

namespace JuliaLean.Markdown

/-! ## `htmlesc` -/

theorem htmlesc_cons (b : Nat) (s : Bytes) : htmlesc (b :: s) = htmlesc [b] ++ htmlesc s := by
  simp [htmlesc]

theorem htmlesc_append (a b : Bytes) : htmlesc (a ++ b) = htmlesc a ++ htmlesc b := by
  simp [htmlesc]

theorem htmlesc_mem (s : Bytes) (x : Nat) (hx : x ∈ htmlesc s) : x ≠ 60 ∧ x ≠ 62 ∧ x ≠ 34 := by
  simp only [htmlesc, List.mem_flatMap] at hx
  obtain ⟨b, -, hb⟩ := hx
  split at hb
  · simp at hb; omega
  · split at hb
    · simp at hb; omega
    · split at hb
      · simp at hb; omega
      · split at hb
        · simp at hb; omega
        · simp at hb
          subst hb
          simp_all

theorem htmlesc_no_lt (s : Bytes) : 60 ∉ htmlesc s := fun h => (htmlesc_mem s 60 h).1 rfl

theorem unesc_one (b : Nat) (t : Bytes) : htmlUnescape (htmlesc [b] ++ t) = b :: htmlUnescape t := by
  by_cases h1 : b = 60
  · subst h1; simp [htmlesc, htmlUnescape]
  by_cases h2 : b = 62
  · subst h2; simp [htmlesc, htmlUnescape]
  by_cases h3 : b = 34
  · subst h3; simp [htmlesc, htmlUnescape]
  by_cases h4 : b = 38
  · subst h4; simp [htmlesc, htmlUnescape]
  have he : htmlesc [b] ++ t = b :: t := by simp [htmlesc, h1, h2, h3, h4]
  rw [he, htmlUnescape.eq_def]
  split <;> simp_all

theorem htmlescSound_proven : HtmlescSound := by
  intro s
  refine ⟨htmlesc_no_lt s, fun h => (htmlesc_mem s 62 h).2.1 rfl,
    fun h => (htmlesc_mem s 34 h).2.2 rfl, ?_⟩
  induction s with
  | nil => rfl
  | cons b s ih => rw [htmlesc_cons, unesc_one, ih]

/-! ## Tag safety -/

theorem isPrefixOf_append (p t u : Bytes) (h : p.isPrefixOf t = true) :
    p.isPrefixOf (t ++ u) = true := by
  induction p generalizing t with
  | nil => simp [List.isPrefixOf]
  | cons a p ih =>
    cases t with
    | nil => simp [List.isPrefixOf] at h
    | cons b t =>
      simp only [List.isPrefixOf, Bool.and_eq_true, List.cons_append] at h ⊢
      exact ⟨h.1, ih t h.2⟩

theorem isPrefixOf_self_append (p u : Bytes) : p.isPrefixOf (p ++ u) = true := by
  induction p with
  | nil => simp [List.isPrefixOf]
  | cons a p ih => simp [List.isPrefixOf, ih]

theorem opensTag_append (t u : Bytes) (h : opensTag t = true) : opensTag (t ++ u) = true := by
  simp only [opensTag, List.any_eq_true] at h ⊢
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (isPrefixOf_append _ _ _ h))
  · exact Or.inl (Or.inr (isPrefixOf_append _ _ _ h))
  · exact Or.inr (isPrefixOf_append _ _ _ h)

theorem opens_gt (n u : Bytes) (hn : n ∈ htmlTagNames) : opensTag (n ++ 62 :: u) = true := by
  simp only [opensTag, List.any_eq_true]
  refine ⟨n, hn, ?_⟩
  have := isPrefixOf_self_append (n ++ [62]) u
  simp only [List.append_assoc, List.singleton_append] at this
  simp [this]

theorem opens_sp (n u : Bytes) (hn : n ∈ htmlTagNames) : opensTag (n ++ 32 :: u) = true := by
  simp only [opensTag, List.any_eq_true]
  refine ⟨n, hn, ?_⟩
  have := isPrefixOf_self_append (n ++ [32]) u
  simp only [List.append_assoc, List.singleton_append] at this
  simp [this]

theorem opens_close (n u : Bytes) (hn : n ∈ htmlTagNames) : opensTag (47 :: (n ++ 62 :: u)) = true := by
  simp only [opensTag, List.any_eq_true]
  refine ⟨n, hn, ?_⟩
  have := isPrefixOf_self_append ([47] ++ n ++ [62]) u
  simp only [List.append_assoc, List.singleton_append, List.cons_append] at this
  simp [this]

theorem tagSafe_append (a b : Bytes) (ha : tagSafe a = true) (hb : tagSafe b = true) :
    tagSafe (a ++ b) = true := by
  induction a with
  | nil => simpa using hb
  | cons x a ih =>
    simp only [tagSafe, Bool.and_eq_true, Bool.or_eq_true, List.cons_append] at ha ⊢
    refine ⟨?_, ih ha.2⟩
    rcases ha.1 with h | h
    · exact Or.inl h
    · exact Or.inr (opensTag_append _ _ h)

theorem tagSafe_of_not_mem (s : Bytes) (h : 60 ∉ s) : tagSafe s = true := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [tagSafe, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
    exact ⟨Or.inl (fun hx => h.1 hx.symm), ih h.2⟩

theorem tagSafe_cons_ne (x : Nat) (t : Bytes) (hx : x ≠ 60) (h : tagSafe t = true) :
    tagSafe (x :: t) = true := by
  simp [tagSafe, hx, h]

theorem tagSafe_cons_lt (t : Bytes) (h1 : opensTag t = true) (h2 : tagSafe t = true) :
    tagSafe (60 :: t) = true := by
  simp [tagSafe, h1, h2]

theorem names_no_lt : ∀ n ∈ htmlTagNames, 60 ∉ n := by decide

theorem attrBytes_no_lt (attrs : List (Bytes × Bytes)) (h : ∀ p ∈ attrs, 60 ∉ p.1) :
    60 ∉ attrBytes attrs := by
  induction attrs with
  | nil => simp [attrBytes]
  | cons p ps ih =>
    rcases p with ⟨a, v⟩
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have h2 := ih h.2
    have hv := htmlesc_no_lt v
    have ha : 60 ∉ a := h.1
    unfold attrBytes at h2 ⊢
    rw [List.flatMap_cons, List.mem_append, not_or]
    refine ⟨?_, h2⟩
    simp [ha, hv]

theorem attrBytes_shape (attrs : List (Bytes × Bytes)) :
    attrBytes attrs = [] ∨ ∃ r, attrBytes attrs = 32 :: r := by
  cases attrs with
  | nil => exact Or.inl rfl
  | cons p ps => exact Or.inr ⟨_, by simp [attrBytes]; rfl⟩

theorem withtag_safe (tag : Bytes) (attrs : List (Bytes × Bytes)) (body : Bytes)
    (htag : tag ∈ htmlTagNames) (hattr : ∀ p ∈ attrs, 60 ∉ p.1) (hbody : tagSafe body = true) :
    tagSafe (withtag tag attrs body) = true := by
  have hn := names_no_lt tag htag
  have ha := attrBytes_no_lt attrs hattr
  have hrest : tagSafe (attrBytes attrs ++ 62 :: (body ++ 60 :: 47 :: (tag ++ [62]))) = true := by
    apply tagSafe_append _ _ (tagSafe_of_not_mem _ ha)
    apply tagSafe_cons_ne _ _ (by decide)
    apply tagSafe_append _ _ hbody
    apply tagSafe_cons_lt
    · exact opens_close tag [] htag
    · apply tagSafe_of_not_mem
      simp [hn]
  have hsafe : tagSafe (60 :: (tag ++ (attrBytes attrs ++ 62 :: (body ++ 60 :: 47 :: (tag ++ [62]))))) = true := by
    apply tagSafe_cons_lt
    · rcases attrBytes_shape attrs with h | ⟨r, h⟩
      · rw [h]; exact opens_gt tag _ htag
      · rw [h]; exact opens_sp tag _ htag
    · exact tagSafe_append _ _ (tagSafe_of_not_mem _ hn) hrest
  simpa [withtag, List.append_assoc] using hsafe

theorem tagOnly_safe (tag : Bytes) (attrs : List (Bytes × Bytes)) (htag : tag ∈ htmlTagNames)
    (hattr : ∀ p ∈ attrs, 60 ∉ p.1) : tagSafe (tagOnly tag attrs) = true := by
  have hn := names_no_lt tag htag
  have ha := attrBytes_no_lt attrs hattr
  have hsafe : tagSafe (60 :: (tag ++ (attrBytes attrs ++ [32, 47, 62]))) = true := by
    apply tagSafe_cons_lt
    · rcases attrBytes_shape attrs with h | ⟨r, h⟩
      · rw [h]; exact opens_sp tag _ htag
      · rw [h]; exact opens_sp tag _ htag
    · exact tagSafe_append _ _ (tagSafe_of_not_mem _ hn)
        (tagSafe_append _ _ (tagSafe_of_not_mem _ ha) (by decide))
  simpa [tagOnly, List.append_assoc] using hsafe

theorem esc_safe (s : Bytes) : tagSafe (htmlesc s) = true := tagSafe_of_not_mem _ (htmlesc_no_lt s)

theorem header_tag (l : Nat) (h1 : 1 ≤ l) (h6 : l ≤ 6) : [104] ++ natDigits l ∈ htmlTagNames := by
  have : ∀ l, l < 7 → 1 ≤ l → [104] ++ natDigits l ∈ htmlTagNames := by decide
  exact this l (by omega) h1

theorem contains_lt (s : Bytes) (h : (!s.contains 60) = true) : 60 ∉ s := by
  simpa using h

mutual
theorem inline_safe (styled : Bytes → Bytes) : (x : Inline) → inlineOk x = true →
    tagSafe (htmlInline styled x) = true
  | .text s, _ => by simp only [htmlInline, htmlText]; exact esc_safe _
  | .code lang c, _ => by
    simp only [htmlInline]
    exact withtag_safe _ _ _ (by decide) (by simp) (esc_safe _)
  | .latex f, _ => by simp only [htmlInline]; exact esc_safe _
  | .bold xs, h => by
    simp only [htmlInline]
    exact withtag_safe _ _ _ (by decide) (by simp) (inlines_safe styled xs (by simpa [inlineOk] using h))
  | .italic xs, h => by
    simp only [htmlInline]
    exact withtag_safe _ _ _ (by decide) (by simp) (inlines_safe styled xs (by simpa [inlineOk] using h))
  | .strike xs, h => by
    simp only [htmlInline]
    exact withtag_safe _ _ _ (by decide) (by simp) (inlines_safe styled xs (by simpa [inlineOk] using h))
  | .link xs url, h => by
    simp only [htmlInline]
    exact withtag_safe _ _ _ (by decide) (by simp) (inlines_safe styled xs (by simpa [inlineOk] using h))
  | .image url alt, _ => by
    simp only [htmlInline]
    exact tagOnly_safe _ _ (by decide) (by simp)
  | .footnoteRef id, h => by
    have hid : 60 ∉ id := contains_lt id (by simpa [inlineOk] using h)
    simp only [htmlInline]
    refine withtag_safe _ _ _ (by decide) (by simp) (tagSafe_of_not_mem _ ?_)
    simp [hid]
  | .lineBreak, _ => by
    simp only [htmlInline]
    exact tagSafe_append _ _ (tagOnly_safe _ _ (by decide) (by simp)) (by decide)
  | .htmlInline _, h => by simp [inlineOk] at h
  | .value r, _ => by simp only [htmlInline]; exact esc_safe _
theorem inlines_safe (styled : Bytes → Bytes) : (xs : List Inline) → inlinesOk xs = true →
    tagSafe (htmlInlines styled xs) = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [inlinesOk, Bool.and_eq_true] at h
    simp only [htmlInlines]
    exact tagSafe_append _ _ (inline_safe styled x h.1) (inlines_safe styled xs h.2)
end

theorem code_block_safe (lang c : Bytes) :
    tagSafe (withtag (bytes% "pre") []
      (withtag (bytes% "code") (if lang.isEmpty then [] else [(bytes% "class", bytes% "language-" ++ lang)])
        (htmlesc c ++ (if c.isEmpty then [] else [10])))) = true := by
  apply withtag_safe _ _ _ (by decide) (by simp)
  apply withtag_safe _ _ _ (by decide) (by split <;> simp)
  apply tagSafe_append _ _ (esc_safe _)
  split <;> decide

mutual
theorem block_safe (styled : Bytes → Bytes) : (b : Block) → blockOk true b = true →
    tagSafe (htmlBlock styled b) = true
  | .para xs, h => by
    simp only [htmlBlock]
    exact withtag_safe _ _ _ (by decide) (by simp) (inlines_safe styled xs (by simpa [blockOk] using h))
  | .header l xs, h => by
    simp only [blockOk, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [htmlBlock]
    exact withtag_safe _ _ _ (header_tag l h.1.1 h.1.2) (by simp) (inlines_safe styled xs h.2)
  | .code lang c, _ => by
    simp only [htmlBlock]
    split <;> exact code_block_safe _ _
  | .latex f, _ => by simp only [htmlBlock]; exact esc_safe _
  | .quote bs, h => by
    simp only [htmlBlock]
    exact withtag_safe _ _ _ (by decide) (by simp)
      (tagSafe_cons_ne _ _ (by decide) (blocks_safe styled bs (by simpa [blockOk] using h)))
  | .list items k loose, h => by
    simp only [htmlBlock]
    apply withtag_safe _ _ _ (by split <;> decide) (by split <;> simp)
    exact tagSafe_append _ _ (items_safe styled loose items (by simpa [blockOk] using h)) (by decide)
  | .hr, _ => by simp only [htmlBlock]; exact tagOnly_safe _ _ (by decide) (by simp)
  | .admonition cat title bs, h => by
    simp only [blockOk, Bool.and_eq_true, Bool.not_true, Bool.false_or] at h
    have ht : 60 ∉ title := contains_lt title h.1
    simp only [htmlBlock]
    refine withtag_safe _ _ _ (by decide) (by simp) (tagSafe_append _ _ ?_ (blocks_safe styled bs h.2))
    exact withtag_safe _ _ _ (by decide) (by simp) (tagSafe_of_not_mem _ ht)
  | .footnote id bs, h => by
    simp only [blockOk, Bool.and_eq_true] at h
    have hid : 60 ∉ id := contains_lt id h.1
    simp only [htmlBlock]
    refine withtag_safe _ _ _ (by decide) (by simp) (tagSafe_append _ _ ?_ (blocks_safe styled bs h.2))
    exact withtag_safe _ _ _ (by decide) (by simp) (tagSafe_of_not_mem _ hid)
  | .htmlBlock _ _, h => by simp [blockOk] at h
  | .value r, _ => by simp only [htmlBlock]; exact esc_safe _
theorem blocks_safe (styled : Bytes → Bytes) : (bs : List Block) → blocksOk true bs = true →
    tagSafe (htmlBlocks styled bs) = true
  | [], _ => rfl
  | b :: bs, h => by
    simp only [blocksOk, Bool.and_eq_true] at h
    simp only [htmlBlocks]
    exact tagSafe_append _ _ (tagSafe_append _ _ (block_safe styled b h.1) (by decide))
      (blocks_safe styled bs h.2)
theorem tight_safe (styled : Bytes → Bytes) : (bs : List Block) → blocksOk true bs = true →
    tagSafe (htmlTight styled bs) = true
  | [], _ => rfl
  | b :: bs, h => by
    simp only [blocksOk, Bool.and_eq_true] at h
    have hb := block_safe styled b h.1
    have hrest := tight_safe styled bs h.2
    cases b with
    | para xs =>
      simp only [htmlTight]
      exact tagSafe_append _ _ (inlines_safe styled xs (by simpa [blockOk] using h.1)) hrest
    | _ => simp only [htmlTight]; exact tagSafe_append _ _ hb hrest
theorem items_safe (styled : Bytes → Bytes) (loose : Bool) : (its : List (List Block)) →
    itemsOk true its = true → tagSafe (htmlItems styled loose its) = true
  | [], _ => rfl
  | it :: its, h => by
    simp only [itemsOk, Bool.and_eq_true] at h
    simp only [htmlItems]
    refine tagSafe_append _ _ (tagSafe_append _ _ (by decide) ?_) (items_safe styled loose its h.2)
    refine withtag_safe _ _ _ (by decide) (by simp) ?_
    split
    · exact tagSafe_cons_ne _ _ (by decide) (blocks_safe styled it h.1)
    · exact tight_safe styled it h.1
end

theorem htmlTagSafeTitles_proven : HtmlTagSafeTitles := fun styled md h => blocks_safe styled md h

end JuliaLean.Markdown
