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

/-- Where a run of exactly `n` backticks starts in `a` from `i` on, before `stop`. -/
def backticksAt (a : Array Char) (stop n i : Nat) : Option Nat := Id.run do
  let mut k := i
  while k < stop do
    if a[k]! == '`' then
      let r := runAt a stop '`' k
      if r == n then return some k
      k := k + r
    else k := k + 1
  return none

/-- Where the mark `m` closes a span whose text starts at `s`, before `stop`: at the
first `m` after something other than a space (and, for `*`, with no star either
side), past escapes and code spans, the text not starting with a space. `**` closes
on the last two of a run of three stars. -/
def closing (a : Array Char) (stop s : Nat) (m : List Char) : Option Nat := Id.run do
  if s ≥ stop || a[s]! == ' ' then return none
  let mut i := s
  while i < stop do
    let c := a[i]!
    if c == '\\' then i := i + 2
    else if c == '`' then
      let n := runAt a stop '`' i
      match backticksAt a stop n (i + n) with
      | some k => i := k + n
      | none => i := i + n
    else
      if s < i && at_ a stop i m && a[i - 1]! != ' ' then
        if m == ['*'] then
          if a[i - 1]! != '*' && get a stop (i + 1) != '*' then return some i
        else if get a stop (i + 2) == '*' then return some (i + 1)
        else return some i
      i := i + 1
  return none

/-- Where `p` first stands in `a` from `i` on, before `stop`. -/
def find (a : Array Char) (stop i : Nat) (p : List Char) : Option Nat := Id.run do
  for k in [i:stop] do
    if at_ a stop k p then return some k
  return none

/-- `a` from `i` to `j` with attributes `at`. -/
def pushRange (acc : Array SChar) (a : Array Char) (i j : Nat) (st : Attrs) : Array SChar := Id.run do
  let mut acc := acc
  for k in [i:j] do acc := acc.push (a[k]!, st)
  return acc

/-- A line's emphasis, code spans, links and escapes from `i` to `stop`, its marks
taken out, after `acc`. -/
partial def inlineGo (a : Array Char) (stop : Nat) (st : Attrs) (i : Nat) (acc : Array SChar) : Array SChar :=
  if i ≥ stop then acc else
  let c := a[i]!
  if c == '\\' && i + 1 < stop && isPunct a[i + 1]! then
    inlineGo a stop st (i + 2) (acc.push (a[i + 1]!, st))
  else if c == '`' then
    let n := runAt a stop '`' i
    match backticksAt a stop n (i + n) with
    | some k => inlineGo a stop st (k + n) (pushRange acc a (i + n) k { st with code := true })
    | none => inlineGo a stop st (i + n) (pushRange acc a i (i + n) st)
  else if c == '*' && get a stop (i + 1) == '*' then
    match closing a stop (i + 2) ['*', '*'] with
    | some k => inlineGo a stop st (k + 2) (inlineGo a k { st with bold := true } (i + 2) acc)
    | none => inlineGo a stop st (i + 1) (acc.push ('*', st))
  else if c == '*' then
    match closing a stop (i + 1) ['*'] with
    | some k => inlineGo a stop st (k + 1) (inlineGo a k { st with italic := true } (i + 1) acc)
    | none => inlineGo a stop st (i + 1) (acc.push ('*', st))
  else if c == '[' then
    match find a stop (i + 1) [']', '('] with
    | some close =>
      match find a stop (close + 2) [')'] with
      | some e =>
        if i + 2 ≤ close then
          let acc := inlineGo a close { st with link := true } (i + 1) acc
          let label := a.extract (i + 1) close
          let url := a.extract (close + 2) e
          let acc := if url.isEmpty || url == label then acc
            else pushRange (acc.push (' ', { st with dim := true })) a (close + 2) e { st with dim := true }
          inlineGo a stop st (e + 1) acc
        else inlineGo a stop st (i + 1) (acc.push ('[', st))
      | none => inlineGo a stop st (i + 1) (acc.push ('[', st))
    | none => inlineGo a stop st (i + 1) (acc.push ('[', st))
  else inlineGo a stop st (i + 1) (acc.push (c, st))

/-- A line's emphasis, code spans, links and escapes, its marks taken out. -/
def inline (st : Attrs) (cs : List Char) : List SChar :=
  let a := cs.toArray
  (inlineGo a a.size st 0 #[]).toList

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

/-- One line that is not part of a code block or a table: a blank, a rule, a
heading, a quote (its rest parsed again under a bar), a list item or text. -/
partial def lineBlock (quote : List SChar) (l : List Char) : Block :=
  let (n, body) := indentOf l
  let ind := styled {} (List.replicate n ' ')
  if body.isEmpty then .text quote quote []
  else if isRule body then .rule quote
  else
    let h := runOf '#' body
    if 1 ≤ h ∧ h ≤ 6 ∧ (body.length = h ∨ body[h]? = some ' ') then
      .text quote quote (inline { heading := true } (body.drop (h + 1)))
    else match body with
    | '>' :: rest =>
      let rest := if rest.head? == some ' ' then rest.tail else rest
      lineBlock (quote ++ bar) rest
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

/-- What the text's lines start with: a code block (its opening fence line, its
lines, and the line that closed it, if one did), a table (its first two lines, their
alignments, and the rows that follow) or one line of its own. A text's blocks
are its groups' in order, each group laid out on its own, so a text can be cut
between groups (`parts`). -/
inductive Group where
  | code (opener : List Char) (body : List (List Char)) (closer : Option (List Char))
  | table (header delim : List Char) (aligns : List Align) (rows : List (List Char))
  | line (l : List Char)

/-- The group the lines `ls` start with, and the lines after it. -/
def group : List (List Char) → Option (Group × List (List Char))
  | [] => none
  | l :: ls =>
    match fence (indentOf l).2 with
    | some f =>
      let body := ls.takeWhile (!closes f ·)
      some (.code l body (ls.drop body.length).head?, ls.drop (body.length + 1))
    | none =>
      match ls with
      | next :: more =>
        match (if hasPipe l then delimiter next else none) with
        | some aligns =>
          if aligns.length == (cells l).length then
            let rows := more.takeWhile fun r => hasPipe r && !(indentOf r).2.isEmpty
            some (.table l next aligns rows, more.drop rows.length)
          else some (.line l, ls)
        | none => some (.line l, ls)
      | [] => some (.line l, [])

/-- A group's blocks. -/
def Group.blocks : Group → List Block
  | .code _ body _ => body.map fun b => .code (styled { code := true } b)
  | .table l next aligns rows =>
    [.table { header := (cells l).map (inline {}), rows := rows.map fun r => (cells r).map (inline {}),
              aligns, raw := l :: next :: rows }]
  | .line l => [lineBlock [] l]

/-- The lines a group was written in. -/
def Group.lines : Group → List (List Char)
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

/-- Whether the line of bytes `b[i:j]` is one `group` reads as a line of its own,
whatever comes before or after it, as it reads an empty line: it holds no pipe, and
the first of its characters after spaces and tabs is no backtick or tilde, so it
neither opens nor closes a code block nor belongs to a table. -/
def plainLine (b : ByteArray) (i j : Nat) : Bool := Id.run do
  let mut lead := true
  for k in [i:j] do
    let x := b[k]!
    if x == '|'.toUInt8 then return false
    if lead && x != ' '.toUInt8 && x != '\t'.toUInt8 then
      if x == '`'.toUInt8 || x == '~'.toUInt8 then return false
      lead := false
  return true

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
  -- Where each line starts; the last start is the text's end when it ends in LF.
  let mut starts : Array Nat := #[0]
  for k in [0:b.size] do
    if b[k]! == 10 then starts := starts.push (k + 1)
  let n := if b[b.size - 1]! == 10 then starts.size - 1 else starts.size
  let start (k : Nat) : Nat := if k < starts.size then starts[k]! else b.size
  -- The text's lines as `parse` reads them, each made harmless on its own (an LF
  -- after a CR makes CR LF one LF), but a plain line, which `group` reads as it
  -- reads an empty one, as one: only lines that may open, close or be in a code
  -- block or a table are decoded.
  let ls : List (List Char) := (List.range n).map fun k =>
    let i := start k
    let j := if k + 1 < starts.size then starts[k + 1]! - 1 else b.size
    if plainLine b i j then [] else
    let j := if k + 1 < starts.size && j > i && b[j - 1]! == 13 then j - 1 else j
    sanitize (String.fromUTF8! (b.extract i j)).toList
  let size' (k : Nat) : Nat := start (k + 1) - start k
  let mut out : Array String := #[]
  -- The current part: the fence line it opens with, if any, and its lines `from`
  -- to `k`, of `bytes`.
  let mut fence : Option Nat := none
  let mut from_ := 0
  let mut bytes := 0
  let mut k := 0
  let mut rest := ls
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
          out := out.push (piece b fence from_ k start)
          fence := none; from_ := k; bytes := 0
        bytes := bytes + size' o
        k := k + 1
        for _ in body do
          -- A part holds a line of the code at least, after its fence line.
          if bytes + size' k > size && k > from_ + (if fence.isSome then 0 else 1) then
            out := out.push (piece b fence from_ k start)
            fence := some o; from_ := k; bytes := size' o
          bytes := bytes + size' k
          k := k + 1
        if c.isSome then bytes := bytes + size' k; k := k + 1
      | g =>
        let m := g.lines.length
        let gb := start (k + m) - start k
        if bytes > 0 && bytes + gb > size then
          out := out.push (piece b fence from_ k start)
          fence := none; from_ := k; bytes := 0
        bytes := bytes + gb
        k := k + m
  if k > from_ then out := out.push (piece b fence from_ k start)
  return out.toList
where
  /-- The part of lines `from_` to `k` of `b`, after the fence line `fence` opens. -/
  piece (b : ByteArray) (fence : Option Nat) (from_ k : Nat) (start : Nat → Nat) : String :=
    let open_ := match fence with
      | some o => b.extract (start o) (start (o + 1))
      | none => ByteArray.empty
    String.fromUTF8! (open_ ++ b.extract (start from_) (start k))

end Markdown
