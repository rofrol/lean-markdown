import Markdown.Layout

/-!
# What the layout guarantees

For a width `w ≥ 2` (a wide character takes two columns):

- `layout_width`: no line of a laid-out document is wider than `w`;
- `layout_source`: the document's text on the lines, with the spaces each break
  took out put back, is the document's text: nothing is lost but the marks the
  parser took out (`Block.content`);
- `layoutTable_wide`: a table too wide for `w` is shown as its lines were written,
  only broken where they reach the edge, so a cell is never cut.
-/

namespace Markdown

def chars (l : List SChar) : List Char := l.map Prod.fst

@[simp] theorem chars_nil : chars [] = [] := rfl

@[simp] theorem chars_append (a b : List SChar) : chars (a ++ b) = chars a ++ chars b := by
  simp [chars]

@[simp] theorem chars_cons (c : SChar) (l : List SChar) : chars (c :: l) = c.1 :: chars l := rfl

@[simp] theorem scols_nil : scols [] = 0 := rfl

@[simp] theorem scols_append (a b : List SChar) : scols (a ++ b) = scols a + scols b := by
  simp [scols]

@[simp] theorem scols_cons (c : SChar) (l : List SChar) : scols (c :: l) = charWidth c.1 + scols l := by
  simp [scols]

/-! ## Characters a row at a time -/

theorem fill_spec (w : Nat) (hw : 2 ≤ w) : ∀ (cs row : List SChar) (col : Nat),
    col = scols row → col ≤ w →
    (∀ x ∈ (fill w row col cs).1, scols x ≤ w) ∧ scols (fill w row col cs).2.1 ≤ w ∧
    (fill w row col cs).2.2 = scols (fill w row col cs).2.1 ∧
    ((fill w row col cs).1.flatMap chars) ++ chars (fill w row col cs).2.1 = chars row ++ chars cs := by
  intro cs
  induction cs with
  | nil => intro row col h1 h2; simp [fill]; omega
  | cons c cs ih =>
    intro row col h1 h2
    have c2 := charWidth_le_two c.1
    unfold fill
    split
    · have := ih (row ++ [c]) (col + charWidth c.1) (by simp; omega) (by omega)
      simpa using this
    · have := ih [c] (charWidth c.1) (by simp) (by omega)
      obtain ⟨a, b, d, e⟩ := this
      refine ⟨?_, b, d, ?_⟩
      · intro x hx
        simp at hx
        rcases hx with rfl | hx
        · omega
        · exact a x hx
      · simp [List.flatMap_cons, e]

theorem hard_spec (w : Nat) (hw : 2 ≤ w) (cs : List SChar) :
    (∀ x ∈ hard w cs, scols x ≤ w) ∧ (hard w cs).flatMap chars = chars cs := by
  obtain ⟨a, b, -, d⟩ := fill_spec w hw cs [] 0 rfl (by omega)
  unfold hard
  refine ⟨?_, ?_⟩
  · intro x hx
    simp at hx
    rcases hx with hx | rfl
    · exact a x hx
    · exact b
  · simpa using d

/-! ## Words -/

/-- The spaces between words are spaces. -/
def Tok.ok : Tok → Prop
  | .word _ => True
  | .gap cs => ∀ c ∈ cs, c.1 = ' '

theorem toks_spec (cs : List SChar) :
    (toks cs).flatMap Tok.chars = cs ∧ ∀ t ∈ toks cs, t.ok := by
  induction cs with
  | nil => simp [toks]
  | cons c cs ih =>
    obtain ⟨ih1, ih2⟩ := ih
    unfold toks
    split
    · next w ts h =>
      rw [h] at ih1 ih2
      split
      · refine ⟨by simp [Tok.chars] at ih1 ⊢; simp [ih1], ?_⟩
        intro t ht
        simp at ht
        rcases ht with rfl | ht
        · simp [Tok.ok]; assumption
        · exact ih2 t (by simp [ht])
      · refine ⟨by simp [Tok.chars] at ih1 ⊢; simp [ih1], ?_⟩
        intro t ht
        simp at ht
        rcases ht with rfl | ht
        · simp [Tok.ok]
        · exact ih2 t (by simp [ht])
    · next g ts h =>
      rw [h] at ih1 ih2
      split
      · refine ⟨by simp [Tok.chars] at ih1 ⊢; simp [ih1], ?_⟩
        intro t ht
        simp at ht
        rcases ht with rfl | ht
        · have := ih2 (.gap g) (by simp)
          simp [Tok.ok] at this ⊢
          constructor
          · assumption
          · exact this
        · exact ih2 t (by simp [ht])
      · refine ⟨by simp [Tok.chars] at ih1 ⊢; simp [ih1], ?_⟩
        intro t ht
        simp at ht
        rcases ht with rfl | rfl | ht
        · simp [Tok.ok]
        · exact ih2 _ (by simp)
        · exact ih2 t (by simp [ht])
    · next h =>
      rw [h] at ih1
      simp at ih1
      subst ih1
      split <;> simp [Tok.chars, Tok.ok] <;> intro a b h <;> subst h <;> assumption

/-- A row's text with the spaces its break took out. -/
def Row.flat (r : Row) : List Char := chars r.body ++ List.replicate r.gap ' '

theorem spaces_chars (sp : List SChar) (h : ∀ c ∈ sp, c.1 = ' ') :
    List.replicate sp.length ' ' = chars sp := by
  induction sp with
  | nil => rfl
  | cons c cs ih =>
    simp [List.replicate_succ] at *
    exact ⟨h.1.symm, ih h.2⟩

theorem fill_rows (w : Nat) (hw : 2 ≤ w) (cs row : List SChar) (col : Nat)
    (h1 : col = scols row) (h2 : col ≤ w) (rest : List Row) (tail : List Char)
    (hr : (∀ x ∈ rest, scols x.body ≤ w) ∧
      rest.flatMap Row.flat = chars (fill w row col cs).2.1 ++ tail) :
    (∀ x ∈ (fill w row col cs).1.map (fun b => (⟨b, 0⟩ : Row)) ++ rest, scols x.body ≤ w) ∧
    ((fill w row col cs).1.map (fun b => (⟨b, 0⟩ : Row)) ++ rest).flatMap Row.flat =
      chars row ++ chars cs ++ tail := by
  obtain ⟨a, -, -, d⟩ := fill_spec w hw cs row col h1 h2
  refine ⟨?_, ?_⟩
  · intro x hx
    simp at hx
    rcases hx with ⟨b, hb, rfl⟩ | hx
    · exact a b hb
    · exact hr.1 x hx
  · rw [List.flatMap_append, hr.2, ← List.append_assoc, ← d]
    simp [Row.flat, List.flatMap_map]

theorem wrapT_spec (w : Nat) (hw : 2 ≤ w) : ∀ (ts : List Tok) (row : List SChar) (col : Nat),
    col = scols row → col ≤ w → (∀ t ∈ ts, t.ok) →
    (∀ r ∈ wrapT w row col ts, scols r.body ≤ w) ∧
    (wrapT w row col ts).flatMap Row.flat = chars row ++ chars (ts.flatMap Tok.chars) := by
  intro ts
  induction ts with
  | nil => intro row col h1 h2 _; simp [wrapT, Row.flat]; omega
  | cons t ts ih =>
    intro row col h1 h2 hok
    have hts : ∀ t ∈ ts, t.ok := fun t ht => hok t (by simp [ht])
    cases t with
    | word ws =>
      simp only [wrapT]
      split
      · have := ih (row ++ ws) (col + scols ws) (by simp; omega) (by omega) hts
        simpa [Tok.chars] using this
      · split
        · next hc =>
          have := ih ws (scols ws) rfl hc.2 hts
          refine ⟨?_, ?_⟩
          · intro r hr
            simp at hr
            rcases hr with rfl | hr
            · simp; omega
            · exact this.1 r hr
          · simp [Row.flat, this.2, Tok.chars]
        · obtain ⟨-, b, c, -⟩ := fill_spec w hw ws row col h1 h2
          have := ih _ _ c (by rw [c]; exact b) hts
          have := fill_rows w hw ws row col h1 h2 _ (chars (ts.flatMap Tok.chars)) this
          simpa [Tok.chars] using this
    | gap sp =>
      have hsp : ∀ c ∈ sp, c.1 = ' ' := hok (.gap sp) (by simp)
      cases ts with
      | nil =>
        simp only [wrapT]
        split
        · simp [Row.flat, Tok.chars]; omega
        · refine ⟨by simp; omega, ?_⟩
          simp [Row.flat, Tok.chars, spaces_chars sp hsp]
      | cons t' ts' =>
        simp only [wrapT]
        split
        · have := ih (row ++ sp) (col + scols sp) (by simp; omega) (by omega) hts
          simpa [Tok.chars] using this
        · split
          · obtain ⟨-, b, c, -⟩ := fill_spec w hw sp row col h1 h2
            have := ih _ _ c (by rw [c]; exact b) hts
            have := fill_rows w hw sp row col h1 h2 _ (chars ((t' :: ts').flatMap Tok.chars)) this
            simpa [Tok.chars] using this
          · have := ih [] 0 rfl (by omega) hts
            refine ⟨?_, ?_⟩
            · intro r hr
              simp at hr
              rcases hr with rfl | hr
              · simp; omega
              · exact this.1 r hr
            · simp only [List.flatMap_cons] at this ⊢
              rw [this.2]
              simp [Row.flat, Tok.chars, spaces_chars sp hsp]

theorem wrap_spec (w : Nat) (hw : 2 ≤ w) (cs : List SChar) :
    (∀ r ∈ wrap w cs, scols r.body ≤ w) ∧ (wrap w cs).flatMap Row.flat = chars cs := by
  obtain ⟨h1, h2⟩ := toks_spec cs
  have := wrapT_spec w hw (toks cs) [] 0 rfl (by omega) h2
  rw [h1] at this
  simpa [wrap] using this

/-! ## Blocks -/

/-- A block's text on the lines `layoutBlock w` makes: what the parser kept of what
was written (a table too wide for `w` keeps all it was written as). -/
def Block.content (w : Nat) : Block → List Char
  | .text _ _ content => chars content
  | .code line => chars line
  | .rule _ => []
  | .table t => if tableFits w t then (t.header :: t.rows).flatMap (·.flatMap chars) else t.raw.flatten

/-- The document's text on the lines of segments. -/
def src (segs : List Seg) : List Char := (segs.filter (!·.added)).flatMap (chars ·.cs)

@[simp] theorem src_nil : src [] = [] := rfl
@[simp] theorem src_append (a b : List Seg) : src (a ++ b) = src a ++ src b := by
  simp [src, List.filter_append]
@[simp] theorem src_cons_added (cs : List SChar) (l : List Seg) : src (⟨cs, true⟩ :: l) = src l := by
  simp [src]
@[simp] theorem src_cons_text (cs : List SChar) (l : List Seg) : src (⟨cs, false⟩ :: l) = chars cs ++ src l := by
  simp [src]

theorem source_eq (o : Out) : o.source = src o.segs ++ List.replicate o.gap ' ' := by
  simp [Out.source, src, chars]

theorem cols_two (a b : List SChar) (x y : Bool) (g : Nat) :
    (Out.mk [⟨a, x⟩, ⟨b, y⟩] g).cols = scols a + scols b := by
  simp [Out.cols]

theorem cols_one (a : List SChar) (x : Bool) (g : Nat) : (Out.mk [⟨a, x⟩] g).cols = scols a := by
  simp [Out.cols]

theorem flat_eq : Row.flat = fun r => chars r.body ++ List.replicate r.gap ' ' := rfl

theorem layoutText_spec (w : Nat) (hw : 2 ≤ w) (lead hang content : List SChar) :
    (∀ o ∈ layoutText w lead hang content, o.cols ≤ w) ∧
    (layoutText w lead hang content).flatMap Out.source = chars content := by
  unfold layoutText
  dsimp only
  split
  · next hp =>
    obtain ⟨h1, h2⟩ := wrap_spec (w - max (scols lead) (scols hang)) (by omega) content
    revert h1 h2
    generalize wrap (w - max (scols lead) (scols hang)) content = rows
    intro h1 h2
    cases rows with
    | nil => simp at h2 ⊢; exact h2
    | cons r rs =>
      simp only
      refine ⟨?_, ?_⟩
      · intro o ho
        simp at ho
        rcases ho with rfl | ⟨r', hr', rfl⟩
        · have := h1 r (by simp); rw [cols_two]; omega
        · have := h1 r' (by simp [hr']); rw [cols_two]; omega
      · rw [← h2]
        simp [source_eq, List.flatMap_map, flat_eq]
  · obtain ⟨h1, h2⟩ := wrap_spec w hw content
    refine ⟨?_, ?_⟩
    · intro o ho
      simp at ho
      obtain ⟨r, hr, rfl⟩ := ho
      rw [cols_one]; exact h1 r hr
    · rw [← h2]
      simp [source_eq, List.flatMap_map, flat_eq]

/-! ## Tables -/

theorem src_cellSegs (cw : Nat) (al : Align) (cell : List SChar) :
    src (cellSegs cw al cell) = chars cell := by
  simp [cellSegs, pad]

theorem src_sep (s : String) : src [sep s] = [] := by simp [sep]

theorem src_lineSegs : ∀ (ws : List Nat) (al : List Align) (r : List (List SChar)),
    r.length ≤ ws.length → src (lineSegs al r ws) = r.flatMap chars := by
  intro ws
  induction ws with
  | nil => intro al r h; simp at h; subst h; simp [lineSegs]
  | cons cw ws ih =>
    intro al r h
    cases ws with
    | nil =>
      simp [lineSegs, src_cellSegs]
      cases r with
      | nil => simp
      | cons c r => simp at h; subst h; simp
    | cons cw' ws' =>
      simp only [lineSegs, src_append, src_cellSegs]
      rw [show (sep " │ " :: lineSegs al.tail r.tail (cw' :: ws')) = [sep " │ "] ++ lineSegs al.tail r.tail (cw' :: ws') from rfl,
        src_append, src_sep, ih al.tail r.tail (by simp at h ⊢; omega)]
      cases r with
      | nil => simp
      | cons c r => simp

theorem flatMap_congr' {α β} {f g : α → List β} {l : List α} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem le_foldl_max (l : List Nat) (init : Nat) : init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => simp; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem mem_le_foldl_max (l : List Nat) (init x : Nat) (h : x ∈ l) : x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at h
  | cons y l ih =>
    simp at h ⊢
    rcases h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max _ _)
    · exact ih _ h

theorem colWidths_length (t : Table) (r : List (List SChar)) (h : r ∈ t.header :: t.rows) :
    r.length ≤ (colWidths t).length := by
  simp only [colWidths, List.length_map, List.length_range]
  exact mem_le_foldl_max _ _ _ (List.mem_map.mpr ⟨r, h, rfl⟩)

theorem chars_boldCell (c : List SChar) : chars (boldCell c) = chars c := by
  simp [boldCell, chars]

theorem src_tableRule (ws : List Nat) : src (tableRule ws).segs = [] := by
  simp only [tableRule]
  induction ws with
  | nil => simp
  | cons cw ws ih =>
    cases ws with
    | nil => simp [sep]
    | cons cw' ws' =>
      simp [List.intersperse_cons_cons, sep] at ih ⊢
      exact ih

theorem layoutTable_spec (w : Nat) (hw : 2 ≤ w) (t : Table) :
    (∀ o ∈ layoutTable w t, o.cols ≤ w) ∧ (layoutTable w t).flatMap Out.source = Block.content w (.table t) := by
  unfold layoutTable Block.content
  split
  · next hf =>
    refine ⟨?_, ?_⟩
    · intro o ho
      simpa using (List.all_eq_true.mp hf) o ho
    · simp only [tableLines, List.flatMap_cons, source_eq, tableLine, List.flatMap_map]
      rw [src_tableRule, src_lineSegs _ _ _ (by simpa using colWidths_length t t.header (by simp))]
      have : ∀ r ∈ t.rows, src (lineSegs t.aligns r (colWidths t)) = r.flatMap chars :=
        fun r hr => src_lineSegs _ _ _ (colWidths_length t r (by simp [hr]))
      simp [List.flatMap_map, chars_boldCell]
      rw [flatMap_congr' this]
      simp [hf, tableRule]
  · next hf =>
    obtain hh := fun l => hard_spec w hw (styled {} l)
    refine ⟨?_, ?_⟩
    · intro o ho
      simp at ho
      obtain ⟨l, -, r, hr, rfl⟩ := ho
      rw [cols_one]; exact (hh l).1 r hr
    · have : ∀ l, (hard w (styled {} l)).flatMap chars = l := fun l => by
        rw [(hh l).2]; simp [styled, chars, Function.comp_def]
      have each : ∀ l ∈ t.raw, (((hard w (styled {} l)).map fun r => (⟨[⟨r, false⟩], 0⟩ : Out)).flatMap
          Out.source) = l := fun l _ => by
        simpa [List.flatMap_map, source_eq, src] using this l
      simp only [hf, List.flatMap_assoc]
      rw [flatMap_congr' each]
      simp

/-- A table that does not fit is shown as written: each of its lines broken only
where it reaches the edge. -/
theorem layoutTable_wide (w : Nat) (t : Table) (h : tableFits w t = false) :
    layoutTable w t = t.raw.flatMap fun l => (hard w (styled {} l)).map fun r => ⟨[⟨r, false⟩], 0⟩ := by
  simp [layoutTable, h]

/-! ## The document -/

theorem layoutBlock_spec (w : Nat) (hw : 2 ≤ w) (b : Block) :
    (∀ o ∈ layoutBlock w b, o.cols ≤ w) ∧ (layoutBlock w b).flatMap Out.source = b.content w := by
  cases b with
  | text lead hang content => exact layoutText_spec w hw lead hang content
  | code line =>
    obtain ⟨h1, h2⟩ := hard_spec w hw line
    refine ⟨?_, ?_⟩
    · intro o ho
      simp [layoutBlock] at ho
      obtain ⟨r, hr, rfl⟩ := ho
      rw [cols_one]; exact h1 r hr
    · simp [layoutBlock, Block.content, List.flatMap_map, source_eq, ← h2]
  | rule lead =>
    simp only [layoutBlock, Block.content]
    split
    · next hp =>
      obtain ⟨h1, -⟩ := hard_spec (w - scols lead) (by omega) (styled dimA (List.replicate ruleWidth '─'))
      refine ⟨?_, ?_⟩
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨r, hr, rfl⟩ := ho
        rw [cols_two]; have := h1 r (List.mem_of_mem_take hr); omega
      · generalize hard (w - scols lead) (styled dimA (List.replicate ruleWidth '─')) = rows
        cases rows <;> simp [source_eq]
    · obtain ⟨h1, -⟩ := hard_spec w hw (styled dimA (List.replicate ruleWidth '─'))
      refine ⟨?_, ?_⟩
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨r, hr, rfl⟩ := ho
        rw [cols_one]; exact h1 r (List.mem_of_mem_take hr)
      · generalize hard w (styled dimA (List.replicate ruleWidth '─')) = rows
        cases rows <;> simp [source_eq]
  | table t => exact layoutTable_spec w hw t

/-- No line of a laid-out document is wider than the width. -/
theorem layout_width (w : Nat) (hw : 2 ≤ w) (d : Doc) : ∀ o ∈ layout w d, o.cols ≤ w := by
  intro o ho
  simp [layout] at ho
  obtain ⟨b, -, hb⟩ := ho
  exact (layoutBlock_spec w hw b).1 o hb

/-- The lines hold the document's text, the spaces taken out at breaks put back:
nothing of it is lost. -/
theorem layout_source (w : Nat) (hw : 2 ≤ w) (d : Doc) :
    (layout w d).flatMap Out.source = d.flatMap (Block.content w) := by
  simp only [layout, List.flatMap_assoc]
  exact flatMap_congr' fun b _ => (layoutBlock_spec w hw b).2

end Markdown
