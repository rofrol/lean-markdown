import Markdown

/-!
# `lake test [DIR]`, `tests --print FILE WIDTH...`

Every fixture of `DIR` (`fixtures/` by default): `NAME.md` rendered at each width
`NAME.txt` names (`== WIDTH` and the lines expected there) must give those lines.
Then each fixture and some generated texts, cut into parts of several sizes
(`Markdown.parts`), must render part after part as they do whole at several widths.
Then a line of about 100 KB of each kind that once took time growing as the square
of its length (thousands of unclosed marks, of backtick runs that close nothing, of
quote bars) must render within ten times as long as a line of plain words as long.
Prints each difference; the exit status is the number of failing sections, cuts
and lines.
`--print` writes what a file renders to, in the fixtures' form, to write one.
-/

open Markdown

/-- The sections of an expected file: each width and its lines. -/
def sections (s : String) : List (Nat × List String) :=
  let ls := (s.splitOn "\n").filter (· != "")
  ls.foldl (init := []) fun acc (l : String) =>
    if l.startsWith "== " then acc ++ [((l.drop 3).toString.toNat!, [])]
    else match acc.getLast? with
      | some (w, xs) => acc.dropLast ++ [(w, xs ++ [l])]
      | none => acc

/-- Whether `text` cut into parts of `size` bytes renders at width `w` as it does
whole (`Markdown.parts`); prints the first difference. -/
def partsAgree (name text : String) (size w : Nat) : IO Bool := do
  let whole := (render text w).map fixtureLine
  let cut := ((parts text size).flatMap (render · w)).map fixtureLine
  if whole == cut then return true
  IO.println s!"FAIL parts of {name} at size {size}, width {w}: {(parts text size).length} parts"
  let k := ((whole.zip cut).takeWhile fun (x, y) => x == y).length
  IO.println s!"  whole, line {k}: {whole[k]?}"
  IO.println s!"  parts, line {k}: {cut[k]?}"
  return false

/-- Texts that cut in every place a part can: code blocks closed and not, with a
language, a longer closing fence and fence-like lines inside, tables, quotes,
lists, CR LF, tabs and blank lines. -/
def partTexts : List (String × String) :=
  let code := String.join ((List.range 40).map fun k => s!"  line {k} ``` not a close\n")
  [("code", s!"intro\n\n```lean\n{code}````  \nafter **bold**\n"),
   ("open code", s!"~~~\n{code}"),
   ("crlf", "a\r\n\tb\r\n```\r\nx\r\n```\r\n| a | b |\r\n| - | - |\r\n| 1 | 2 |\r\n"),
   ("mixed", String.join ((List.range 30).map fun k =>
      s!"## Step {k}\n\n> quote {k}\n- item `c{k}`\n| N | V |\n| --- | ---: |\n| a{k} | {k} |\n\n```\n{k}\n```\n"))]

/-- `piece` repeated to about `size` characters. -/
def repeatTo (size : Nat) (piece : String) : String :=
  String.join (List.replicate (size / piece.length + 1) piece)

/-- Long lines of each kind that once took time growing as the square of their
length: marks no mark closes, backtick runs no run closes (after an escape, and of
every length up to about 450), quote bars with and without spaces. -/
def slowLines : List (String × String) :=
  let size := 100000
  [("unclosed *", repeatTo size "a *b "), ("unclosed **", repeatTo size "a **b "),
   ("unclosed [", repeatTo size "[a "), ("links without )", repeatTo size "[a](b "),
   ("escaped backticks", repeatTo size "\\`` "),
   ("backtick runs of each length", " ".intercalate ((List.range 446).map fun k => String.ofList (List.replicate (k + 1) '`'))),
   ("quote bars", repeatTo size ">"), ("spaced quote bars", repeatTo size "> ")]

/-- The nanoseconds `text` took to render at width 80. -/
def renderNanos (text : String) : IO Nat := do
  let t0 ← IO.monoNanosNow
  -- The width read from the clock, and the lines' count used, so that the render is
  -- neither moved out of the timed span nor left out.
  let n := (render text (if t0 == 0 then 81 else 80)).length
  let t1 ← IO.monoNanosNow
  if n == 0 then IO.println "(no lines)"
  return t1 - t0

/-- The fewest nanoseconds `plain` and `text` took to render, in three runs of each
taken in turn, so that both are timed in the same stretch of the machine's load. -/
def pairNanos (plain text : String) : IO (Nat × Nat) := do
  let mut p := 0
  let mut t := 0
  for k in [0:3] do
    let x ← renderNanos plain
    let y ← renderNanos text
    if k == 0 || x < p then p := x
    if k == 0 || y < t then t := y
  return (p, t)

def main (args : List String) : IO UInt32 := do
  if let "--print" :: file :: widths := args then
    let md ← IO.FS.readFile file
    for w in widths do
      IO.println s!"== {w}"
      for l in render md w.toNat! do IO.println (fixtureLine l)
    return 0
  let dir : System.FilePath := args.headD "fixtures"
  let entries ← dir.readDir
  let names := (entries.filter fun e => e.fileName.endsWith ".md" && e.fileName != "README.md").map (·.fileName) |>.qsort (· < ·)
  if names.isEmpty then
    IO.eprintln s!"no fixtures in {dir}"
    return 1
  let mut bad : UInt32 := 0
  let mut count := 0
  for n in names do
    let base := (n.dropEnd 3).toString
    let md ← IO.FS.readFile (dir / n)
    let some expected ← (some <$> IO.FS.readFile (dir / (base ++ ".txt"))) <|> pure none
      | IO.println s!"FAIL {base}: no {base}.txt"; bad := bad + 1
    for (w, want) in sections expected do
      count := count + 1
      let got := (render md w).map fixtureLine
      if got != want then
        bad := bad + 1
        IO.println s!"FAIL {base} at {w}:"
        IO.println "  expected:"
        for l in want do IO.println s!"    {l}"
        IO.println "  got:"
        for l in got do IO.println s!"    {l}"
  IO.println s!"{count - bad.toNat} of {count} sections pass"
  -- Every fixture and every generated text cut at several sizes renders as whole.
  let mut texts := partTexts
  for n in names do texts := texts ++ [(n, ← IO.FS.readFile (dir / n))]
  let mut cuts := 0
  let mut cutsBad := 0
  for (name, text) in texts do
    for size in [1, 16, 64, 300] do
      for w in [2, 9, 30, 80] do
        cuts := cuts + 1
        unless ← partsAgree name text size w do cutsBad := cutsBad + 1
  -- A code block is cut between its lines: no part holds more than `size` bytes
  -- and its fence, nor, of lines longer than half of `size`, more than one.
  let code := (partTexts.lookup "open code").getD ""
  if (parts code 64).any (·.utf8ByteSize > 64 + 4) || (parts code 64).length < 10 then
    IO.println s!"FAIL parts of open code: {(parts code 64).map (·.utf8ByteSize)} bytes"
    cutsBad := cutsBad + 1
  let long := "~~~\n" ++ String.join (List.replicate 10 (String.ofList (List.replicate 49 'x') ++ "\n"))
  if (parts long 60).map (·.utf8ByteSize) != List.replicate 10 54 then
    IO.println s!"FAIL parts of long code lines: {(parts long 60).map (·.utf8ByteSize)} bytes"
    cutsBad := cutsBad + 1
  IO.println s!"{cuts - cutsBad} of {cuts} cuts render as the whole text"
  bad := bad + cutsBad.toUInt32
  -- Each slow kind of line within ten times a plain line as long: a line of 100 KB
  -- that takes time as the square of its length is hundreds of times slower.
  let plainText := repeatTo 100000 "word "
  let mut slowBad := 0
  for (name, text) in slowLines do
    let (plain, t) ← pairNanos plainText text
    if t > 10 * plain then
      IO.println s!"FAIL {name}: {t / 1000000} ms for {text.length} characters, plain words {plain / 1000000} ms"
      slowBad := slowBad + 1
  IO.println s!"{slowLines.length - slowBad} of {slowLines.length} long lines render as fast as plain words"
  return bad + slowBad.toUInt32
