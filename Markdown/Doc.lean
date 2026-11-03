import Markdown.Width

/-!
# The document

What `Markdown.parse` makes of a text and `Markdown.layout` lays out. Text is held
as characters with their attributes, so what is kept and what is cut can be proved
about (`Markdown.Proofs`).
-/

namespace Markdown

/-- How a character is drawn: any of these at once (a bold word in a heading is
both). A viewer maps them to its colours. -/
structure Attrs where
  heading : Bool := false
  bold : Bool := false
  italic : Bool := false
  code : Bool := false
  link : Bool := false
  dim : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A character with its attributes. -/
abbrev SChar := Char × Attrs

def scols (l : List SChar) : Nat := cols (l.map Prod.fst)

/-- `s` as characters, all with attributes `a`. -/
def styled (a : Attrs) (s : List Char) : List SChar := s.map (·, a)

inductive Align where
  | left | center | right
  deriving DecidableEq, Repr, Inhabited

/-- A table: its header, its rows and each column's alignment, and the lines it was
written in, which a table too wide for the width shows instead. -/
structure Table where
  header : List (List SChar)
  rows : List (List (List SChar))
  aligns : List Align
  raw : List (List Char)
  deriving Repr, Inhabited

inductive Block where
  /-- A line of text: a paragraph's, a list item's, a heading's or a quote's.
  `lead` goes before its first row and `hang` before the others, as wide as `lead`:
  quote bars, indentation and a list's marker. -/
  | text (lead hang : List SChar) (content : List SChar)
  /-- A line of a code block, as written. -/
  | code (line : List SChar)
  /-- A rule (`---`), after `lead`: a quote's bars. -/
  | rule (lead : List SChar)
  | table (t : Table)
  deriving Repr, Inhabited

abbrev Doc := List Block

/-- A piece of a laid-out line: text of the document, or text the layout adds
(`added`): prefixes, padding, a table's separators and a rule. -/
structure Seg where
  cs : List SChar
  added : Bool := false
  deriving Repr, Inhabited

/-- A line laid out, and the spaces taken out where it was broken from the next. -/
structure Out where
  segs : List Seg
  gap : Nat := 0
  deriving Repr, Inhabited

def Out.cols (o : Out) : Nat := (o.segs.map fun s => scols s.cs).sum

/-- The document's text on a line, and the spaces its break took out. -/
def Out.source (o : Out) : List Char :=
  (o.segs.filter (!·.added)).flatMap (·.cs.map Prod.fst) ++ List.replicate o.gap ' '

/-- A run of text in one style, as a viewer draws it. -/
structure Span where
  text : String
  attrs : Attrs
  deriving DecidableEq, Repr, Inhabited

/-- A line's segments as spans, neighbours of the same attributes merged. -/
def Out.spans (o : Out) : List Span :=
  let cs := o.segs.flatMap (·.cs)
  let groups := cs.splitBy fun a b => a.2 == b.2
  groups.filterMap fun g => g.head?.map fun h => { text := String.ofList (g.map Prod.fst), attrs := h.2 }

end Markdown
