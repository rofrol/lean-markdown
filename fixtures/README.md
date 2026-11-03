# The fixtures

One set of cases for lean-markdown and odin-markdown
(https://github.com/rofrol/odin-markdown), so both lay out a document the same:
odin-markdown's checks read this directory, not a copy of it.

Each case is `NAME.md`, a text as Claude writes it, and `NAME.txt`, the lines it
lays out to: a line `== WIDTH`, then each line laid out at that width, for as many
widths as the case names. A line is written as its spans: each as `<` and its
attributes' letters and `>`, then its text, a `<` in the text doubled; `$` ends the
line, so trailing spaces stay visible. The letters, in this order: `h` heading, `b`
bold, `i` italic, `c` code, `l` link, `d` dim; `<>` is plain. Neighbouring spans of
the same attributes are one span.

    == 40
    <h>A <hb>bold<h> heading$
    <d>• <>one$

To add a case, write `NAME.md`, render it (`.lake/build/bin/tests --print
fixtures/NAME.md WIDTH...` in lean-markdown), check every line against the subset
in `README.md` by hand, and only then keep it as `NAME.txt`.

Widths below 2 are not supported (a wide character needs two columns): the cases
at width 1 pin what both libraries do there, nothing more.
