import Lake
open Lake DSL

package «lean-markdown»

/-- Columns and text broken into rows, counted as rr's viewers count them:
lean-tui, the user's own library, pinned by commit. -/
require «lean-tui» from git "https://github.com/rofrol/lean-tui" @ "e0181aecc7ce282f5a498182dd8117f7f52e5dd9"

/-- The library, `Markdown.*`: pure Lean, no C, on lean-tui's pure modules. -/
@[default_target]
lean_lib Markdown

/-- `lake test`: every fixture of `fixtures/` at each of its widths. -/
@[test_driver]
lean_exe tests where
  srcDir := "Tests"
  root := `Main
