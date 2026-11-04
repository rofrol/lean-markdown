import Markdown

/-!
# `lake test [DIR]`, `tests --print FILE WIDTH...`

Every fixture of `DIR` (`fixtures/` by default): `NAME.md` rendered at each width
`NAME.txt` names (`== WIDTH` and the lines expected there) must give those lines.
Then each fixture and some generated texts, cut into parts of several sizes
(`Markdown.parts`), must render part after part as they do whole at several widths.
Prints each difference; the exit status is the number of failing sections and
cuts.
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
  return bad
