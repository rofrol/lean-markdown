import Markdown.Width
import Markdown.Doc
import Markdown.Parse
import Markdown.Layout
import Markdown.Fixture
import Markdown.Proofs

/-!
# lean-markdown

    Markdown.render text width : List (List Markdown.Span)

The Markdown Claude writes, laid out for a terminal: `README.md`.
-/

namespace Markdown

/-- A text's lines laid out `w` columns wide, each as spans of one style. -/
def render (text : String) (w : Nat) : List (List Span) :=
  (layout w (parse text)).map Out.spans

end Markdown
