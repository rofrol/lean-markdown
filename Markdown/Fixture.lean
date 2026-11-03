import Markdown.Doc

/-!
# The fixtures' form

How a laid-out line is written in a fixture (`fixtures/README.md`): each span as its
attributes' letters in `<…>` (`h` heading, `b` bold, `i` italic, `c` code, `l` link,
`d` dim; none for plain) and its text, a `<` of the text doubled, the line ended by
`$`.
-/

namespace Markdown

def Attrs.letters (a : Attrs) : String :=
  (if a.heading then "h" else "") ++ (if a.bold then "b" else "") ++
  (if a.italic then "i" else "") ++ (if a.code then "c" else "") ++
  (if a.link then "l" else "") ++ (if a.dim then "d" else "")

def Span.fixture (s : Span) : String :=
  "<" ++ s.attrs.letters ++ ">" ++ s.text.replace "<" "<<"

def fixtureLine (spans : List Span) : String := String.join (spans.map Span.fixture) ++ "$"

end Markdown
