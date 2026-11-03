import Lake
open Lake DSL

package «lean-markdown»

/-- The library, `Markdown.*`: pure Lean, no C. -/
@[default_target]
lean_lib Markdown

/-- `lake test`: every fixture of `fixtures/` at each of its widths. -/
@[test_driver]
lean_exe tests where
  srcDir := "Tests"
  root := `Main
