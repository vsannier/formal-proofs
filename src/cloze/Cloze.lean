-- See <https://docs.ankiweb.net/editing.html#cloze-deletion>.

inductive ClozeText where
  | text : String → ClozeText
  | cloze : Nat → ClozeText → String → ClozeText
  | append : ClozeText → ClozeText → ClozeText

def ClozeText.fold {α : Type} (clz : ClozeText)
    (onText : String → α)
    (onCloze : Nat → α → String → α)
    (onAppend : α → α → α) : α :=
  match clz with
  | ClozeText.text txt => onText txt
  | ClozeText.cloze n body hint =>
      onCloze n (body.fold onText onCloze onAppend) hint
  | ClozeText.append left right =>
      onAppend
        (left.fold onText onCloze onAppend)
        (right.fold onText onCloze onAppend)

def ClozeText.size (clz : ClozeText) : Nat :=
  clz.fold
    (fun _ => 1)
    (fun _ body _ => body + 1)
    (fun left right => left + right + 1)

def ClozeText.maxIndex (clz : ClozeText) : Nat :=
  clz.fold
    (fun _ => 0)
    (fun n body _ => max n body)
    max

-- Escape characters that have special meaning in cloze syntax.
private def escapeChar : Char → List Char
  | ':' => "&#58;".toList
  | '{' => "&#123;".toList
  | '}' => "&#125;".toList
  | char => [char]

def escape (txt : String) : String :=
  String.ofList (txt.toList.flatMap escapeChar)

theorem escape_append (left right : String) :
    escape (left ++ right) = escape left ++ escape right := by
  simp [escape]

@[simp]
theorem escape_empty : escape "" = "" :=
  rfl

theorem escape_idempotent (txt : String) :
    escape (escape txt) = escape txt := by
  simp only [escape, String.toList_ofList]
  apply congrArg String.ofList
  induction txt.toList with
  | nil => rfl
  | cons char chars ih =>
      simp only [List.flatMap_cons, List.flatMap_append, ih, escapeChar]
      split <;> simp [escapeChar]

def render (clz : ClozeText) : String :=
  clz.fold
    escape
    (fun n body hint =>
      "{{c" ++ toString n ++ "::" ++ body ++ "::" ++ escape hint ++ "}}")
    (fun left right => left ++ right)

example :
    render
      (ClozeText.append
        (ClozeText.text "The capital of France is ")
        (ClozeText.cloze 1 (ClozeText.text "Paris") "city")) =
      "The capital of France is {{c1::Paris::city}}" := by
  rfl

def reveal (clz : ClozeText) (n : Nat) : String :=
  clz.fold
    id
    (fun m body hint => if m = n then hint else body)
    (fun left right => left ++ right)

def SameReveals (left right : ClozeText) : Prop :=
  ∀ n, reveal left n = reveal right n

theorem SameReveals.refl (clz : ClozeText) : SameReveals clz clz :=
  fun _ => rfl

theorem SameReveals.symm {left right : ClozeText}
    (same : SameReveals left right) : SameReveals right left :=
  fun index => (same index).symm

theorem SameReveals.trans {left middle right : ClozeText}
    (leftMiddle : SameReveals left middle)
    (middleRight : SameReveals middle right) :
    SameReveals left right :=
  fun index => (leftMiddle index).trans (middleRight index)

theorem SameReveals.isEquivalence : Equivalence SameReveals :=
  ⟨SameReveals.refl, SameReveals.symm, SameReveals.trans⟩

-- Remove empty text nodes and merge adjacent text.
def simplify (clz : ClozeText) : ClozeText :=
  match clz with
  | ClozeText.text txt => ClozeText.text txt
  | ClozeText.cloze n body hint =>
      ClozeText.cloze n (simplify body) hint
  | ClozeText.append left right =>
      match simplify left, simplify right with
      | ClozeText.text "", right => right
      | left, ClozeText.text "" => left
      | ClozeText.text left, ClozeText.text right =>
          ClozeText.text (left ++ right)
      | left, right => ClozeText.append left right

def IsSimple (clz : ClozeText) : Prop :=
  clz = simplify clz

-- Abstract the proof that simplification preserves meaning.
structure SimplifyLaws {α : Type}
    (onText : String → α)
    (onAppend : α → α → α) : Prop where
  emptyLeft : ∀ value, onAppend (onText "") value = value
  emptyRight : ∀ value, onAppend value (onText "") = value
  appendText : ∀ left right,
    onText (left ++ right) = onAppend (onText left) (onText right)

theorem ClozeText.fold_simplify {α : Type}
    (onText : String → α)
    (onCloze : Nat → α → String → α)
    (onAppend : α → α → α)
    (laws : SimplifyLaws onText onAppend)
    (clz : ClozeText) :
    (simplify clz).fold onText onCloze onAppend =
      clz.fold onText onCloze onAppend := by
  rcases laws with ⟨emptyLeft, emptyRight, appendText⟩
  induction clz with
  | text _ =>
      rfl
  | cloze _ _ _ ih =>
      simp [simplify, ClozeText.fold, ih]
  | append left right _ _ =>
      simp only [simplify]
      split <;> simp_all [ClozeText.fold]

theorem simplify_decreases_size (clz : ClozeText) :
    (simplify clz).size ≤ clz.size := by
  induction clz with
  | text _ =>
      exact Nat.le_refl _
  | cloze _ _ _ ih =>
      simpa [simplify, ClozeText.size, ClozeText.fold] using
        Nat.add_le_add_right ih 1
  | append left right _ _ =>
      simp only [simplify]
      split <;>
        simp_all [ClozeText.size, ClozeText.fold] <;>
        omega

theorem maxIndex_simplify (clz : ClozeText) :
    (simplify clz).maxIndex = clz.maxIndex := by
  unfold ClozeText.maxIndex
  apply ClozeText.fold_simplify
  constructor <;> simp

theorem simplify_idempotent (clz : ClozeText) :
    simplify (simplify clz) = simplify clz := by
  induction clz with
  | text _ =>
      rfl
  | cloze _ _ _ ih =>
      simp [simplify, ih]
  | append left right _ _ =>
      simp only [simplify]
      split <;> simp_all [simplify]

theorem simplify_isSimple (clz : ClozeText) :
    IsSimple (simplify clz) := by
  exact (simplify_idempotent clz).symm

theorem render_simplify (clz : ClozeText) :
    render (simplify clz) = render clz := by
  unfold render
  apply ClozeText.fold_simplify
  constructor <;> simp [escape_append]

theorem simplify_sound (clz : ClozeText) :
    SameReveals (simplify clz) clz := by
  intro index
  unfold reveal
  apply ClozeText.fold_simplify
  constructor <;> simp

-- Unused indices all produce the same revealed text.
theorem reveal_eq_above_maxIndex (clz : ClozeText) {m n : Nat}
    (hm : clz.maxIndex < m) (hn : clz.maxIndex < n) :
    reveal clz m = reveal clz n := by
  induction clz with
  | text _ =>
      rfl
  | cloze index body hint ih =>
      change max index body.maxIndex < m at hm
      change max index body.maxIndex < n at hn
      change (if index = m then hint else reveal body m) =
        if index = n then hint else reveal body n
      by_cases hmIndex : index = m
      · omega
      · by_cases hnIndex : index = n
        · omega
        · simp only [hmIndex, hnIndex, reduceIte]
          apply ih <;> omega
  | append left right ihLeft ihRight =>
      change max left.maxIndex right.maxIndex < m at hm
      change max left.maxIndex right.maxIndex < n at hn
      change reveal left m ++ reveal right m =
        reveal left n ++ reveal right n
      rw [
        ihLeft (by omega) (by omega),
        ihRight (by omega) (by omega)
      ]

-- SameReveals is determined by finitely many observations.
theorem sameReveals_iff_bounded (left right : ClozeText) :
    SameReveals left right ↔
      ∀ n : Fin (max left.maxIndex right.maxIndex + 2),
        reveal left n = reveal right n := by
  constructor
  · intro same index
    exact same index
  · intro bounded index
    let bound := max left.maxIndex right.maxIndex + 1
    by_cases hIndex : index ≤ bound
    · exact bounded ⟨index, by omega⟩
    · calc
        reveal left index = reveal left bound :=
          by apply reveal_eq_above_maxIndex <;> omega
        _ = reveal right bound := bounded ⟨bound, by omega⟩
        _ = reveal right index := by
          apply reveal_eq_above_maxIndex <;> omega

instance sameReveals_decidable (left right : ClozeText) :
    Decidable (SameReveals left right) :=
  decidable_of_iff
    (∀ n : Fin (max left.maxIndex right.maxIndex + 2),
      reveal left n = reveal right n)
    (sameReveals_iff_bounded left right).symm

theorem cloze_redundant_iff (n : Nat) (body : ClozeText) (hint : String) :
    SameReveals (ClozeText.cloze n body hint) body ↔
      hint = reveal body n := by
  constructor
  · intro same
    simpa [reveal, ClozeText.fold] using same n
  · intro hHint index
    by_cases hIndex : n = index
    · subst index
      simpa [reveal, ClozeText.fold] using hHint
    · simp [reveal, ClozeText.fold, hIndex]

theorem distinct_clozes_commute {m n : Nat} (hDistinct : m ≠ n)
    (body : ClozeText) (hintM hintN : String) :
    SameReveals
      (ClozeText.cloze m (ClozeText.cloze n body hintN) hintM)
      (ClozeText.cloze n (ClozeText.cloze m body hintM) hintN) := by
  intro index
  by_cases hm : m = index
  · subst index
    simp [reveal, ClozeText.fold, hDistinct.symm]
  · by_cases hn : n = index
    · subst index
      simp [reveal, ClozeText.fold, hDistinct]
    · simp [reveal, ClozeText.fold, hm, hn]

def representCards (cards : List String) (start : Nat := 1) : ClozeText :=
  match cards with
  | [] => ClozeText.text ""
  | card :: cards =>
      ClozeText.cloze start (representCards cards (start + 1)) card

theorem representCards_correct (cards : List String) (start : Nat)
    (index : Fin cards.length) :
    reveal (representCards cards start) (start + index.val) =
      cards[index] := by
  induction cards generalizing start with
  | nil =>
      exact Fin.elim0 index
  | cons card cards ih =>
      induction index using Fin.cases with
      | zero =>
          simp [representCards, reveal, ClozeText.fold]
      | succ index =>
          simp only [representCards, reveal, ClozeText.fold]
          rw [ite_eq_right (by simp [Fin.succ])]
          change reveal (representCards cards (start + 1))
            (start + (index.val + 1)) = cards[index]
          rw [← Nat.add_assoc, Nat.add_right_comm start index.val 1]
          exact ih (start + 1) index

def IsRepresentable (cards : List String) : Prop :=
  ∃ clz : ClozeText, ∀ index : Fin cards.length,
    reveal clz (index.val + 1) = cards[index]

theorem all_cards_representable (cards : List String) :
    IsRepresentable cards :=
  ⟨representCards cards, fun index => by
    simpa [Nat.add_comm] using representCards_correct cards 1 index⟩
