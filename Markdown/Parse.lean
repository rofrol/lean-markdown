import Markdown.Doc

/-!
# Parsing

The Markdown Claude writes, parsed a line at a time into blocks (`README.md`, The
subset). What is not Markdown of the subset stays as written.
-/

namespace Markdown

open Tui (charWidth cols)
open Tui.Words

/-- The text made harmless and even: CR LF becomes LF, a tab four spaces, and every
other control character (C0 but LF, DEL, C1; ESC too, so no sequence reaches a
terminal) U+FFFD, the rest of a sequence staying as text. -/
def sanitize : List Char → List Char
  | [] => []
  | '\r' :: '\n' :: cs => '\n' :: sanitize cs
  | '\t' :: cs => ' ' :: ' ' :: ' ' :: ' ' :: sanitize cs
  | c :: cs =>
    let n := c.toNat
    if c ≠ '\n' ∧ (n < 0x20 ∨ (0x7f ≤ n ∧ n < 0xa0)) then '�' :: sanitize cs
    else c :: sanitize cs

/-- The text's lines; an LF at its end ends the last one. -/
def lines (cs : List Char) : List (List Char) :=
  let ls := cs.splitOn '\n'
  if cs.getLast? = some '\n' then ls.dropLast else if cs = [] then [] else ls

def isPunct (c : Char) : Bool := "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList.contains c

/-- The character at `k` of `a` when `k` is before `stop`, else a space. -/
def get (a : Array Char) (stop k : Nat) : Char := if k < stop then a[k]! else ' '

/-- Whether `m` stands in `a` at `k`, before `stop`. -/
def at_ (a : Array Char) (stop k : Nat) (m : List Char) : Bool := Id.run do
  let mut i := k
  for c in m do
    if i ≥ stop || a[i]! != c then return false
    i := i + 1
  return true

/-- The length of the run of `c` at `i` in `a`, before `stop`. -/
def runAt (a : Array Char) (stop : Nat) (c : Char) (i : Nat) : Nat := Id.run do
  let mut n := 0
  for k in [i:stop] do
    if a[k]! != c then break
    n := n + 1
  return n

/-- The length of the run of `c` that starts `cs`. -/
def runOf (c : Char) (cs : List Char) : Nat := (cs.takeWhile (· == c)).length

/-- What `inlineGo` looks up in a line, found once for the whole line, so that no
mark scans the rest of its line again for each opener: on a line of thousands of
unclosed marks that would take time growing as the square of its length.

Every `stop` `inlineGo` is called with is the line's end, or where a span's closing
mark (`*`, `**`) or a link's `](` stands, so no run of backticks crosses it and
what holds of a run in the whole line holds of it before `stop`. -/
structure Line where
  a : Array Char
  /-- For each `k` where a backtick stands: where the code span a run from `k` on
  opens closes, the first whole run of as many backticks after it, as a scan run by
  run finds it; else, and where no backtick stands, `a.size`. -/
  tick : Array Nat
  /-- For each `k` up to `a.size`: where `](` first stands from `k` on, else
  `a.size`. -/
  link : Array Nat
  /-- For each `k` up to `a.size`: where `)` first stands from `k` on, else
  `a.size`. -/
  paren : Array Nat

/-- For each `k` up to `a.size`, where `p` first stands in `a` from `k` on, else
`a.size`. -/
def nextOf (a : Array Char) (p : List Char) : Array Nat := Id.run do
  let n := a.size
  let mut out := Array.replicate (n + 1) n
  for j in [0:n] do
    let k := n - 1 - j
    out := out.set! k (if at_ a n k p then k else out[k + 1]!)
  return out

/-- The line `a` and what `inlineGo` looks up in it, read from its end: the run of
backticks from each `k` on and, by length, the first whole run seen so far. -/
def Line.of (a : Array Char) : Line := Id.run do
  let n := a.size
  let mut run := Array.replicate (n + 1) 0
  let mut first := Array.replicate (n + 1) n
  let mut tick := Array.replicate n n
  for j in [0:n] do
    let k := n - 1 - j
    if a[k]! == '`' then
      let r := run[k + 1]! + 1
      run := run.set! k r
      tick := tick.set! k first[r]!
      if k == 0 || a[k - 1]! != '`' then first := first.set! r k
  return { a, tick, link := nextOf a [']', '('], paren := nextOf a [')'] }

/-- Where the code span the run of `n` backticks at `i` opens closes, before `stop`. -/
def Line.codeClose (L : Line) (stop i n : Nat) : Option Nat :=
  let k := L.tick[i]!
  if k + n ≤ stop then some k else none

/-- Where `p`, of `len` characters and looked up in `next` (`Line.link` or
`Line.paren`), first stands from `i` on, before `stop`: where it first stands in the
whole line, when that is before `stop`, as every later place is after it. -/
def firstAt (next : Array Nat) (stop i len : Nat) : Option Nat :=
  let k := next[i]!
  if k + len ≤ stop then some k else none

/-- Where the mark `m` closes a span whose text starts at `s`, before `stop`: at the
first `m` after something other than a space (and, for `*`, with no star either
side), past escapes and code spans, the text not starting with a space. `**` closes
on the last two of a run of three stars.

`fail` holds, of each place a scan for `m` reached after its start, `stop + 1` of
that scan, and is returned with the places this scan reached. Where a scan goes
next depends on where it is alone, and whether a place closes on that place alone
but for its start, so a scan that reaches a place an earlier one at the same `stop`
reached goes the same way from there. That one failed: had it found a closing mark,
`inlineGo` would have gone on after that mark at that `stop`, where no scan reaches
what that one reached. So each place is scanned once per mark and `stop`. -/
def closing (L : Line) (fail : Array Nat) (stop s : Nat) (m : List Char) : Option Nat × Array Nat := Id.run do
  let a := L.a
  if s ≥ stop || a[s]! == ' ' then return (none, fail)
  let mut fail := fail
  let mut i := s
  while i < stop do
    if s < i then
      if fail[i]! == stop + 1 then return (none, fail)
      fail := fail.set! i (stop + 1)
    let c := a[i]!
    if c == '\\' then i := i + 2
    else if c == '`' then
      let n := runAt a stop '`' i
      match L.codeClose stop i n with
      | some k => i := k + n
      | none => i := i + n
    else
      if s < i && at_ a stop i m && a[i - 1]! != ' ' then
        if m == ['*'] then
          if a[i - 1]! != '*' && get a stop (i + 1) != '*' then return (some i, fail)
        else if get a stop (i + 2) == '*' then return (some (i + 1), fail)
        else return (some i, fail)
      i := i + 1
  return (none, fail)

/-- `a` from `i` to `j` with attributes `at`. -/
def pushRange (acc : Array SChar) (a : Array Char) (i j : Nat) (st : Attrs) : Array SChar := Id.run do
  let mut acc := acc
  for k in [i:j] do acc := acc.push (a[k]!, st)
  return acc

/-- A line's emphasis, code spans, links and escapes from `i` to `stop`, its marks
taken out, after `acc`; `star` and `bold` are `closing`'s `fail` for `*` and `**`,
returned with the output. -/
partial def inlineGo (L : Line) (stop : Nat) (st : Attrs) (i : Nat) (acc : Array SChar)
    (star bold : Array Nat) : Array SChar × Array Nat × Array Nat :=
  let a := L.a
  if i ≥ stop then (acc, star, bold) else
  let c := a[i]!
  if c == '\\' && i + 1 < stop && isPunct a[i + 1]! then
    inlineGo L stop st (i + 2) (acc.push (a[i + 1]!, st)) star bold
  else if c == '`' then
    let n := runAt a stop '`' i
    match L.codeClose stop i n with
    | some k => inlineGo L stop st (k + n) (pushRange acc a (i + n) k { st with code := true }) star bold
    | none => inlineGo L stop st (i + n) (pushRange acc a i (i + n) st) star bold
  else if c == '*' && get a stop (i + 1) == '*' then
    match closing L bold stop (i + 2) ['*', '*'] with
    | (some k, bold) =>
      let (acc, star, bold) := inlineGo L k { st with bold := true } (i + 2) acc star bold
      inlineGo L stop st (k + 2) acc star bold
    | (none, bold) => inlineGo L stop st (i + 1) (acc.push ('*', st)) star bold
  else if c == '*' then
    match closing L star stop (i + 1) ['*'] with
    | (some k, star) =>
      let (acc, star, bold) := inlineGo L k { st with italic := true } (i + 1) acc star bold
      inlineGo L stop st (k + 1) acc star bold
    | (none, star) => inlineGo L stop st (i + 1) (acc.push ('*', st)) star bold
  else if c == '[' then
    match firstAt L.link stop (i + 1) 2 with
    | some close =>
      match firstAt L.paren stop (close + 2) 1 with
      | some e =>
        if i + 2 ≤ close then
          let (acc, star, bold) := inlineGo L close { st with link := true } (i + 1) acc star bold
          let label := a.extract (i + 1) close
          let url := a.extract (close + 2) e
          let acc := if url.isEmpty || url == label then acc
            else pushRange (acc.push (' ', { st with dim := true })) a (close + 2) e { st with dim := true }
          inlineGo L stop st (e + 1) acc star bold
        else inlineGo L stop st (i + 1) (acc.push ('[', st)) star bold
      | none => inlineGo L stop st (i + 1) (acc.push ('[', st)) star bold
    | none => inlineGo L stop st (i + 1) (acc.push ('[', st)) star bold
  else inlineGo L stop st (i + 1) (acc.push (c, st)) star bold

/-- A line's emphasis, code spans, links and escapes, its marks taken out. -/
def inline (st : Attrs) (cs : List Char) : List SChar :=
  let L := Line.of cs.toArray
  let n := L.a.size
  (inlineGo L n st 0 #[] (Array.replicate n 0) (Array.replicate n 0)).1.toList

/-- The leading spaces of a line, and the rest. -/
def indentOf (l : List Char) : Nat × List Char :=
  let n := runOf ' ' l
  (n, l.drop n)

/-- A fence that opens a code block: its character and length. -/
def fence (body : List Char) : Option (Char × Nat) :=
  match body with
  | c :: _ => if (c == '`' || c == '~') && runOf c body ≥ 3 then some (c, runOf c body) else none
  | [] => none

/-- Whether a line closes a code block its fence `(c, n)` opened. -/
def closes (f : Char × Nat) (l : List Char) : Bool :=
  let body := (indentOf l).2
  runOf f.1 body ≥ f.2 && (body.drop (runOf f.1 body)).all (· == ' ')

def isRule (body : List Char) : Bool :=
  let marks := body.filter (· != ' ')
  match marks with
  | c :: _ => marks.length ≥ 3 && (c == '-' || c == '*' || c == '_') && marks.all (· == c)
  | [] => false

/-- A table row's cells: split at each pipe no backslash escapes, a leading and a
trailing pipe dropped (trailing spaces aside), each cell trimmed and `\|` made `|`. -/
def cells (l : List Char) : List (List Char) := Id.run do
  let body := ((indentOf l).2.reverse.dropWhile (· == ' ')).reverse
  let mut out : Array (List Char) := #[]
  let mut cur : Array Char := #[]
  let mut rest := body
  let mut trailing := false
  while !rest.isEmpty do
    match rest with
    | '\\' :: '\\' :: r => cur := (cur.push '\\').push '\\'; rest := r
    | '\\' :: '|' :: r => cur := cur.push '|'; rest := r
    | '|' :: r => out := out.push cur.toList; cur := #[]; rest := r; trailing := r.isEmpty
    | c :: r => cur := cur.push c; rest := r
    | [] => rest := []
  if !trailing then out := out.push cur.toList
  let trim (c : List Char) : List Char := ((c.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse
  let cs := if body.head? == some '|' then out.toList.drop 1 else out.toList
  return cs.map trim

/-- Whether a line holds a pipe no backslash escapes. -/
def hasPipe (l : List Char) : Bool := Id.run do
  let mut prev := ' '
  for c in l do
    if c == '|' && prev != '\\' then return true
    prev := if prev == '\\' && c == '\\' then ' ' else c
  return false

/-- A delimiter row's alignments, one cell at least: each cell `-`s with an optional
`:` at either end. -/
def delimiter (l : List Char) : Option (List Align) :=
  if !hasPipe l then none else
  let cs := cells l
  if cs.isEmpty then none else
  let one (c : List Char) : Option Align :=
    let left := c.head? == some ':'
    let right := c.getLast? == some ':' && c.length > 1
    let mid := (c.drop (if left then 1 else 0)).take (c.length - (if left then 1 else 0) - (if right then 1 else 0))
    if mid.isEmpty || !mid.all (· == '-') then none
    else some (if left && right then .center else if right then .right else .left)
  cs.mapM one

def bar : List SChar := styled { dim := true } "│ ".toList

/-- How many quote bars `>` a line starts with, each after spaces and before an
optional space, and the rest of it, after `d` bars found already; `fuel`, the
line's length, bounds the bars. A loop, not a call per bar, so that a line of
thousands of bars takes time as its length. -/
def quotes : Nat → Nat → List Char → Nat × List Char
  | 0, d, l => (d, l)
  | fuel + 1, d, l =>
    match (indentOf l).2 with
    | '>' :: rest => quotes fuel (d + 1) (if rest.head? == some ' ' then rest.tail else rest)
    | _ => (d, l)

/-- One line that is not part of a code block or a table: a blank, a rule, a
heading, a quote (its rest read as a line under a bar), a list item or text. A
`>` after spaces always starts a quote, as no blank, rule or heading starts
with it, so the bars are taken first. -/
def lineBlock (l : List Char) : Block :=
  let (d, l) := quotes l.length 0 l
  let quote := (List.replicate d bar).flatten
  let (n, body) := indentOf l
  let ind := styled {} (List.replicate n ' ')
  if body.isEmpty then .text quote quote []
  else if isRule body then .rule quote
  else
    let h := runOf '#' body
    if 1 ≤ h ∧ h ≤ 6 ∧ (body.length = h ∨ body[h]? = some ' ') then
      .text quote quote (inline { heading := true } (body.drop (h + 1)))
    else match body with
    | m :: ' ' :: rest =>
      if m == '-' || m == '*' || m == '+' then
        let marker := styled { dim := true } "• ".toList
        .text (quote ++ ind ++ marker) (quote ++ ind ++ styled {} "  ".toList) (inline {} rest)
      else ordered quote ind body
    | _ => ordered quote ind body
where
  /-- `1. ` or `1) `, its number kept; else a line of text. -/
  ordered (quote ind : List SChar) (body : List Char) : Block :=
    let d := (body.takeWhile Char.isDigit).length
    match body.drop d with
    | p :: ' ' :: rest =>
      if 1 ≤ d ∧ d ≤ 9 ∧ (p == '.' || p == ')') then
        let marker := styled {} (body.take (d + 2))
        .text (quote ++ ind ++ marker) (quote ++ ind ++ styled {} (List.replicate (d + 2) ' ')) (inline {} rest)
      else .text (quote ++ ind) (quote ++ ind) (inline {} body)
    | _ => .text (quote ++ ind) (quote ++ ind) (inline {} body)

/-- What `group` reads of a line `α`: the fence it opens a code block with, whether it
closes the code block a fence opened, whether it holds a pipe no backslash escapes,
whether it is blank after spaces, its alignments as a table's delimiter row, and its
count of cells. A line of characters (`List Char`) is read by the functions above;
`parts` reads a text's lines as `Shape`s, found from their bytes, which answer only
what `group` asks where it asks it: `closes` of a fence `fence` found, `cols` of a
line with a pipe above a delimiter row. -/
class GroupLine (α : Type) where
  fence : α → Option (Char × Nat)
  closes : Char × Nat → α → Bool
  hasPipe : α → Bool
  blank : α → Bool
  delimiter : α → Option (List Align)
  cols : α → Nat

instance : GroupLine (List Char) where
  fence l := Markdown.fence (indentOf l).2
  closes := Markdown.closes
  hasPipe := Markdown.hasPipe
  blank l := (indentOf l).2.isEmpty
  delimiter := Markdown.delimiter
  cols l := (cells l).length

/-- What the text's lines start with: a code block (its opening fence line, its
lines, and the line that closed it, if one did), a table (its first two lines, their
alignments, and the rows that follow) or one line of its own. A text's blocks
are its groups' in order, each group laid out on its own, so a text can be cut
between groups (`parts`). -/
inductive Group (α : Type) where
  | code (opener : α) (body : List α) (closer : Option α)
  | table (header delim : α) (aligns : List Align) (rows : List α)
  | line (l : α)

/-- The group the lines `ls` start with, and the lines after it. -/
def group [GroupLine α] : List α → Option (Group α × List α)
  | [] => none
  | l :: ls =>
    match GroupLine.fence l with
    | some f =>
      let body := ls.takeWhile (!GroupLine.closes f ·)
      some (.code l body (ls.drop body.length).head?, ls.drop (body.length + 1))
    | none =>
      match ls with
      | next :: more =>
        match (if GroupLine.hasPipe l then GroupLine.delimiter next else none) with
        | some aligns =>
          if aligns.length == GroupLine.cols l then
            let rows := more.takeWhile fun r => GroupLine.hasPipe r && !GroupLine.blank r
            some (.table l next aligns rows, more.drop rows.length)
          else some (.line l, ls)
        | none => some (.line l, ls)
      | [] => some (.line l, [])

/-- A group's blocks. -/
def Group.blocks : Group (List Char) → List Block
  | .code _ body _ => body.map fun b => .code (styled { code := true } b)
  | .table l next aligns rows =>
    [.table { header := (cells l).map (inline {}), rows := rows.map fun r => (cells r).map (inline {}),
              aligns, raw := l :: next :: rows }]
  | .line l => [lineBlock l]

/-- The lines a group was written in. -/
def Group.lines : Group α → List α
  | .code o body c => o :: body ++ c.toList
  | .table l next _ rows => l :: next :: rows
  | .line l => [l]

/-- The blocks of the text's lines. -/
partial def blocks (ls : List (List Char)) : List Block :=
  match group ls with
  | none => []
  | some (g, rest) => g.blocks ++ blocks rest

/-- A text as a document. -/
def parse (text : String) : Doc := blocks (lines (sanitize text.toList))

/-- What `group` reads of a line of a text's bytes (`GroupLine`), found from its bytes
(`shapes`) without decoding it. -/
structure Shape where
  /-- The backtick or tilde the line starts with after spaces, the length of its
  run, and whether only spaces follow the run. -/
  mark : Option (Char × Nat × Bool)
  pipe : Bool
  blank : Bool
  /-- Its alignments as a delimiter row. -/
  delim : Option (List Align)
  /-- Its count of cells where it holds a pipe and the next line is a delimiter
  row, the only place `group` reads it; else 0. -/
  cols : Nat
  deriving Inhabited

/-- `closes f` is read only of a fence `fence` found, of three marks or more, so a
line that starts with no mark closes none. -/
instance : GroupLine Shape where
  fence s := match s.mark with
    | some (c, n, _) => if n ≥ 3 then some (c, n) else none
    | none => none
  closes f s := match s.mark with
    | some (c, n, rest) => c == f.1 && n ≥ f.2 && rest
    | none => false
  hasPipe s := s.pipe
  blank s := s.blank
  delimiter s := s.delim
  cols s := s.cols

/-- Where the line from `k` of `b` ends, at its LF or the end of `b`, and whether it
holds a pipe no backslash escapes, as `hasPipe` reads it: `bs` whether the byte before
`k` is a backslash no backslash escapes. No byte of a character of more than one
byte, nor a control character's (which `sanitize` makes U+FFFD), is a backslash or a
pipe, so the bytes read as the characters do. -/
def lineEnd (b : ByteArray) (k : Nat) (bs pipe : Bool) : Nat × Bool :=
  if h : k < b.size then
    let x := b[k]
    if x == 10 then (k, pipe)
    else lineEnd b (k + 1) (x == 92 && !bs) (pipe || (x == 124 && !bs))
  else (k, pipe)
termination_by b.size - k

/-- The first place from `k` before `j` in `b` that holds no byte of `ok`, else `j`. -/
def skipWhile (b : ByteArray) (ok : UInt8 → Bool) (k j : Nat) : Nat :=
  if h : k < j ∧ k < b.size then
    if ok b[k] then skipWhile b ok (k + 1) j else k
  else k
termination_by j - k

def isWs (x : UInt8) : Bool := x == 32 || x == 9

/-- The line `b[i:j]` without the spaces and tabs at either end, as `[p, q)`. -/
def trimmed (b : ByteArray) (i j : Nat) : Nat × Nat :=
  let p := skipWhile b isWs i j
  let rec back (q : Nat) : Nat :=
    if q > p then if isWs b[q - 1]! then back (q - 1) else q else q
  termination_by q
  (p, back j)

/-- The count of cells of the line `b[i:j]` as `cells` splits it: one more than its
pipes no backslash escapes, less the one it starts with after spaces and the one it
ends with before them. -/
def cellCount (b : ByteArray) (i j : Nat) : Nat :=
  let (p, q) := trimmed b i j
  -- The pipes from `k` on, and whether the last byte before `q` is one.
  let rec go (k : Nat) (bs : Bool) (n : Nat) (last : Bool) : Nat × Bool :=
    if h : k < q ∧ k < b.size then
      let x := b[k]
      let pipe := x == 124 && !bs
      go (k + 1) (x == 92 && !bs) (if pipe then n + 1 else n) (pipe && k + 1 == q)
    else (n, last)
  termination_by q - k
  let (n, last) := go p false 0 false
  n + (if last then 0 else 1) - (if p < q && b[p]! == 124 then 1 else 0)

/-- The alignments of the line `b[i:j]` as `delimiter` reads it, when it holds
nothing but spaces, tabs, pipes, colons and dashes, which a delimiter row holds,
so no backslash escapes a pipe in it; else `none`. -/
def delimAt (b : ByteArray) (i j : Nat) : Option (List Align) := Id.run do
  let (p, q) := trimmed b i j
  -- The cells between pipes; the first is dropped where the line starts with a
  -- pipe, the last where it ends with one.
  let mut out : Array Align := #[]
  let mut c := if p < q && b[p]! == 124 then p + 1 else p
  for _ in [0:q - p + 1] do
    if c ≥ q then break
    let e := skipWhile b (· != 124) c q
    let (s, t) := trimmed b c e
    let left := s < t && b[s]! == 58
    let right := t > s + 1 && b[t - 1]! == 58
    let ms := if left then s + 1 else s
    let mt := if right then t - 1 else t
    if ms ≥ mt || skipWhile b (· == 45) ms mt != mt then return none
    out := out.push (if left && right then .center else if right then .right else .left)
    c := e + 1
  if out.isEmpty then return none
  return some out.toList

/-- The shape of each of the text's lines `b`, as `group` reads the line `parse`
makes of it, and where each line starts, the text's end last when it ends in LF:
one pass over the bytes, a tab and a space being alike to `group` (`sanitize` makes
a tab spaces) and a CR before an LF no part of its line (`sanitize` makes CR LF an
LF). A line is read as a delimiter row only when it holds a pipe and nothing but
spaces, tabs, pipes, colons and dashes (a delimiter row holds nothing else), and
the line above one for its count of cells. -/
def shapes (b : ByteArray) : Array Shape × Array Nat := Id.run do
  let mut out : Array Shape := #[]
  let mut starts : Array Nat := #[0]
  let mut i := 0
  -- Each turn reads a line; a text of n bytes has at most n lines.
  for _ in [0:b.size] do
    if i ≥ b.size then break
    let (e, pipe) := lineEnd b i false false
    let j := if e < b.size && e > i && b[e - 1]! == 13 then e - 1 else e
    let p := skipWhile b isWs i j
    let mark := if p < j && (b[p]! == 96 || b[p]! == 126) then
        let q := skipWhile b (· == b[p]!) p j
        some (Char.ofNat b[p]!.toNat, q - p, skipWhile b isWs q j == j)
      else none
    let delim := if pipe && skipWhile b (fun x => isWs x || x == 124 || x == 58 || x == 45) i j == j
      then delimAt b i j else none
    out := out.push { mark, pipe, blank := p == j, delim, cols := 0 }
    if delim.isSome && out.size ≥ 2 && out[out.size - 2]!.pipe then
      let o := starts[starts.size - 2]!
      let oj := if i - 1 > o && b[i - 2]! == 13 then i - 2 else i - 1
      out := out.modify (out.size - 2) ({ · with cols := cellCount b o oj })
    if e < b.size then starts := starts.push (e + 1)
    i := e + 1
  return (out, starts)

/-- The text cut into parts of about `size` bytes that lay out as the whole text
does, part after part: `render text w` is the parts' `render`s in order at every
width (checked by `lake test` over every fixture and generated texts). A text of at
most `size` bytes is its one part. Else each part is whole lines of the text, cut
after an LF, so making each part harmless (`sanitize`) makes the text's lines; cut
between the groups `group` reads, and within a code block between its lines, the
next part opening the block again with its fence line, which draws nothing, the part
before running to its end, as a code block no line closes does. A part is larger
than `size` only by one group that is not a code block (a line, a table) or by a
code block's fence line. Lets a viewer lay out a large text a part at a time. -/
def parts (text : String) (size : Nat) : List String := Id.run do
  if text.utf8ByteSize ≤ size then return [text]
  let b := text.toUTF8
  -- The text's lines as `group` reads them, and where each starts.
  let (ls, starts) := shapes b
  let n := ls.size
  let start (k : Nat) : Nat := if k < starts.size then starts[k]! else b.size
  let size' (k : Nat) : Nat := start (k + 1) - start k
  let mut out : Array String := #[]
  -- The current part: the fence line it opens with, if any, and its lines `from`
  -- to `k`, of `bytes`.
  let mut fence : Option Nat := none
  let mut from_ := 0
  let mut bytes := 0
  let mut k := 0
  let mut rest := ls.toList
  -- Each turn takes a group; a text of n lines has at most n groups.
  for _ in [0:n] do
    match group rest with
    | none => break
    | some (g, r) =>
      rest := r
      match g with
      | .code _ body c =>
        let o := k
        if bytes > 0 && bytes + size' o + size' (o + 1) > size then
          out := out.push (piece text fence from_ k start)
          fence := none; from_ := k; bytes := 0
        bytes := bytes + size' o
        k := k + 1
        for _ in body do
          -- A part holds a line of the code at least, after its fence line.
          if bytes + size' k > size && k > from_ + (if fence.isSome then 0 else 1) then
            out := out.push (piece text fence from_ k start)
            fence := some o; from_ := k; bytes := size' o
          bytes := bytes + size' k
          k := k + 1
        if c.isSome then bytes := bytes + size' k; k := k + 1
      | g =>
        let m := g.lines.length
        let gb := start (k + m) - start k
        if bytes > 0 && bytes + gb > size then
          out := out.push (piece text fence from_ k start)
          fence := none; from_ := k; bytes := 0
        bytes := bytes + gb
        k := k + m
  if k > from_ then out := out.push (piece text fence from_ k start)
  return out.toList
where
  /-- The part of lines `from_` to `k` of `text`, after the fence line `fence` opens:
  copied by byte offsets, each the text's start or end or after an LF, so on a
  character's boundary. -/
  piece (text : String) (fence : Option Nat) (from_ k : Nat) (start : Nat → Nat) : String :=
    let cut (i j : Nat) := String.Pos.Raw.extract text ⟨i⟩ ⟨j⟩
    match fence with
    | some o => cut (start o) (start (o + 1)) ++ cut (start from_) (start k)
    | none => cut (start from_) (start k)

end Markdown
