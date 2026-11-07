# lean-markdown

The Markdown Claude writes, parsed into a typed document and laid out for a
terminal of a given width as lines of styled spans, in Lean 4, with theorems.
odin-markdown (https://github.com/rofrol/odin-markdown) is the same in Odin; both
are checked against the fixtures here (`fixtures/README.md`).

    import Markdown
    Markdown.render text width : List (List Markdown.Span)   -- each line's spans
    Markdown.parse text : Markdown.Doc
    Markdown.layout width doc : List Markdown.Out
    Markdown.parts text size : List String              -- render part after part

A span is text and its attributes (`heading`, `bold`, `italic`, `code`, `link`,
`dim`, any of them at once); a viewer maps them to its colours.

## What is proved

For every width `w ≥ 2` and every document (`Markdown/Proofs.lean`):

- `layout_width`: no line is wider than `w` columns, counted by `charWidth`: two for
  East Asian Width W and F of Unicode 17.0.0, else one (lean-tui's `Tui.Width`, the
  count rr's viewers use). A line of text is broken between words by lean-tui's
  `Tui.Words.wrap`, and code and a table too wide by `Tui.Words.hard`, whose
  theorems (`wrap_spec`, `hard_spec`) these build on.
- `layout_source`: the lines hold the document's text: put back the spaces taken
  out where a line was broken and leave out what the layout added (prefixes,
  padding, a table's separators, a rule), and what is left is the document's text,
  so nothing but the parser's marks is lost.
- `layoutTable_spec` and `layoutTable_wide`: a table is in columns only when every
  line of it fits, and then holds every cell whole on its row; otherwise it is
  shown as its lines were written, only broken where they reach the edge. No cell
  is ever cut short.

The document's text there (`Block.content`) is what the parser kept: it leaves out
list markers, quote bars and a table's pipes, which the layout draws again (and a
prefix left out at a narrow width is not drawn). That `render`'s spans regroup the
lines without changing them is not proved.

What the parser keeps of a text is not proved but pinned by the fixtures.

`parts` cuts a large text into parts of about a given size, between the groups
the parser reads (a line, a table, a code block, which is cut between its lines and
opened again with its fence), so a viewer can lay it out a part at a time: the
parts render, one after another, as the whole text does. Not proved either:
`lake test` checks it for every fixture and for generated texts at several sizes
and widths. A part is larger than the size only by one line or one table.
It reads what the grouping needs of each line from the line's bytes
(`shapes`), decoding none; `lake test` checks that every line of those texts
reads so as its characters do, and that the lines group alike.

A line takes time about as its length to lay out, also a line of thousands of
marks nothing closes, of backtick runs no run closes or of quote bars: no mark
scans the rest of its line again for each opener. Not proved: `lake test` checks
that a line of about 100 KB of each such kind renders within ten times as long as a
line of plain words as long.

## The subset

The text is first made harmless: CR LF becomes LF, a tab four spaces, and every
other control character (C0 but LF, DEL, C1, so ESC too) becomes U+FFFD, the rest
of an escape sequence staying as text, so nothing in it reaches a terminal as a
command. Then each line is one block, but for code blocks and tables:

- A fence of three or more backticks or tildes opens a code block, up to a line
  of the same character at least as long, or the end. The fences and the
  language name are not shown; the code is, as written, broken at the edge.
- A table: a line with a pipe, then a delimiter row (`---`, `:--`, `--:`, `:-:`
  cells) with as many cells, then every following line with a pipe. Cells split at
  each pipe no backslash escapes (inside code spans too, as GFM does); `\|` is
  a pipe; a leading and a trailing pipe are dropped. A row may have fewer cells
  (they are empty) or more (the table gets more columns: nothing is dropped). In
  columns: ` │ ` between columns, the header bold over a `─┼─` rule, each column
  aligned as its delimiter says. A table cut off after its delimiter row is a
  table with no rows. A table is a block: laid out again for each width.
- A blank line is an empty line. `---`, `***`, `___` (three or more, spaces
  between allowed) are a rule, 20 columns of `─` or the width.
- `#` to `######` and a space make a heading; `>` a quote, its rest laid out again
  after a `│ ` bar; `- `, `* `, `+ ` a list item with a `• ` marker; `1. ` or
  `1) ` (up to nine digits) an ordered item, its number kept. Else a line of text.
  Leading spaces are kept before list items and text, and dropped before the rest.
- Within a line: `**bold**`, `*italic*`, `` `code` `` (a run of backticks closed
  by a run as long, nothing inside parsed), `[label](url)` shown as the label and
  then the url, dimmed, unless it is empty or the label itself; a backslash before
  ASCII punctuation shows that punctuation. A mark opens only before something
  other than a space and closes only after something other than a space; a mark
  nothing closes stays as written, so `2 * 3 * 4` and `*.md` stay. `***x***` is
  bold italic. `_` is not a mark (it is in names). A url ends at its first `)`.

Lines break between words; a word wider than the row breaks at the edge, and the
spaces where a line breaks are taken out. A list item's or quote's later rows start
under its text; when its prefix leaves less than two columns, the prefix is left
out. Each source line stays a line of its own, as Claude's text expects.

## Toolchain

`lean-toolchain` is the nightly rr builds with,
`leanprover/lean4-nightly:nightly-2026-10-25`: rr builds this library with its own
toolchain, so this one is tested on that. It moves to the first stable release
that holds the fix rr waits for, together with rr.

    lake build        # the library; also checks every theorem
    lake test         # every fixture at each of its widths, parts, long lines

It builds on lean-tui (https://github.com/rofrol/lean-tui), required from the
checkout beside this one (`../lean-tui`) until lean-tui is published and pinned
by commit.

MIT, `LICENSE`.
