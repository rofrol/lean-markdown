import Markdown.Doc

/-!
# Parsing

The Markdown Claude writes, parsed a line at a time into blocks (`README.md`, The
subset). What is not Markdown of the subset stays as written.
-/

namespace Markdown

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

/-- The blocks of the text's lines. -/
partial def blocks : List (List Char) → List Block
  | [] => []
  | l :: ls =>
    match fence (indentOf l).2 with
    | some f =>
      let body := ls.takeWhile (!closes f ·)
      body.map (fun b => .code (styled { code := true } b)) ++ blocks (ls.drop (body.length + 1))
    | none =>
      match ls with
      | next :: more =>
        match (if hasPipe l then delimiter next else none) with
        | some aligns =>
          let header := cells l
          if aligns.length == header.length then
            let body := more.takeWhile fun r => hasPipe r && !(indentOf r).2.isEmpty
            let t : Table := {
              header := header.map (inline {})
              rows := body.map fun r => (cells r).map (inline {})
              aligns, raw := l :: next :: body }
            .table t :: blocks (more.drop body.length)
          else lineBlock [] l :: blocks ls
        | none => lineBlock [] l :: blocks ls
      | [] => [lineBlock [] l]

/-- A text as a document. -/
def parse (text : String) : Doc := blocks (lines (sanitize text.toList))

end Markdown
