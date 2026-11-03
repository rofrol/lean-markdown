import Markdown

/-!
# `lake test [DIR]`, `tests --print FILE WIDTH...`

Every fixture of `DIR` (`fixtures/` by default): `NAME.md` rendered at each width
`NAME.txt` names (`== WIDTH` and the lines expected there) must give those lines.
Prints each difference; the exit status is the number of failing sections.
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
  return bad
