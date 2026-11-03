import Markdown.Doc

/-!
# Layout

A document laid out for a terminal `w` columns wide: no line wider than `w` (for
`w ≥ 2`, as a wide character needs two), and every character of the document kept,
but the spaces where a line of text is broken (`Markdown.Proofs`).
-/

namespace Markdown

open Tui (charWidth cols)
open Tui.Words

def dimA : Attrs := { dim := true }
def boldA : Attrs := { bold := true }

/-- The columns of a table: each the widest of its cells, at least one. -/
def colWidths (t : Table) : List Nat :=
  let all := t.header :: t.rows
  let n := (all.map List.length).foldl max 0
  (List.range n).map fun j => (all.map fun r => scols (r.getD j [])).foldl max 1

def pad (n : Nat) : Seg := ⟨styled {} (List.replicate n ' '), true⟩

/-- A cell padded to `cw` columns as its column aligns it. -/
def cellSegs (cw : Nat) (al : Align) (cell : List SChar) : List Seg :=
  let room := cw - scols cell
  let left := match al with
    | .left => 0
    | .right => room
    | .center => room / 2
  [pad left, ⟨cell, false⟩, pad (room - left)]

def sep (s : String) : Seg := ⟨styled dimA s.toList, true⟩

/-- A row's cells in columns `ws`, a ` │ ` between each two; a cell it lacks is
empty. -/
def lineSegs : List Align → List (List SChar) → List Nat → List Seg
  | _, _, [] => []
  | al, r, [cw] => cellSegs cw (al.headD .left) (r.headD [])
  | al, r, cw :: ws => cellSegs cw (al.headD .left) (r.headD []) ++ sep " │ " :: lineSegs al.tail r.tail ws

def tableLine (ws : List Nat) (aligns : List Align) (r : List (List SChar)) : Out :=
  ⟨lineSegs aligns r ws, 0⟩

def tableRule (ws : List Nat) : Out :=
  ⟨((ws.map fun cw => [sep (String.ofList (List.replicate cw '─'))]).intersperse [sep "─┼─"]).flatten, 0⟩

def boldCell (c : List SChar) : List SChar := c.map fun (ch, a) => (ch, { a with bold := true })

/-- A table in columns, its header bold over a rule. -/
def tableLines (t : Table) : List Out :=
  let ws := colWidths t
  tableLine ws t.aligns (t.header.map boldCell) :: tableRule ws :: t.rows.map (tableLine ws t.aligns)

/-- Whether a table in columns fits in `w`. -/
def tableFits (w : Nat) (t : Table) : Bool := (tableLines t).all (·.cols ≤ w)

/-- A table in columns when it fits in `w`; else the lines it was written in,
broken where they reach the edge: a cell is never cut. -/
def layoutTable (w : Nat) (t : Table) : List Out :=
  if tableFits w t then tableLines t
  else t.raw.flatMap fun l => (hard w (styled {} l)).map fun r => ⟨[⟨r, false⟩], 0⟩

/-- A line of text: `lead` before its first row and `hang` before the rest, when
they leave it two columns; else none. -/
def layoutText (w : Nat) (lead hang content : List SChar) : List Out :=
  let pw := max (scols lead) (scols hang)
  if pw + 2 ≤ w then
    match wrap (w - pw) content with
    | [] => []
    | r :: rs => ⟨[⟨lead, true⟩, ⟨r.body, false⟩], r.gap⟩ ::
        rs.map fun r => ⟨[⟨hang, true⟩, ⟨r.body, false⟩], r.gap⟩
  else (wrap w content).map fun r => ⟨[⟨r.body, false⟩], r.gap⟩

def ruleWidth : Nat := 20

def layoutBlock (w : Nat) : Block → List Out
  | .text lead hang content => layoutText w lead hang content
  | .code line => (hard w line).map fun r => ⟨[⟨r, false⟩], 0⟩
  | .rule lead =>
    let line := styled dimA (List.replicate ruleWidth '─')
    if scols lead + 2 ≤ w then ((hard (w - scols lead) line).take 1).map fun r => ⟨[⟨lead, true⟩, ⟨r, true⟩], 0⟩
    else ((hard w line).take 1).map fun r => ⟨[⟨r, true⟩], 0⟩
  | .table t => layoutTable w t

/-- A document laid out `w` columns wide. -/
def layout (w : Nat) (d : Doc) : List Out := d.flatMap (layoutBlock w)

end Markdown
