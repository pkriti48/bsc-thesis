import Game.Metadata

namespace Word

World "AppendAndConcat"
Level 1

Title "Append an Empty Word to a Non-Empty Word"

Introduction "In the first level of this game, you will prove that appending the empty word ```nil```
to a non-empty word ```word``` results into ```word```."

/--
```append_nil``` is the proof of ```word ++ nil = word```.

```append_nil``` proves, whenever you append the empty word ```nil``` to a non-empty word, the
resulting term is always the non-empty word.
You almost always want to simplify the expression on the left-hand side of the ```=``` sign  and
bring to the state on the right-hand side, which can be done by using the ```rewrite``` tactic.
-/
TheoremDoc append_nil as "append_nil" in "Word"

Statement append_nil (word : Word) : (word ++ nil) = word := by
  Hint "You should start by induction on ```word```."
  induction word with
  | nil =>
    Hint (hidden := true) "At this point, you can simplify the proof goal by executing
    ```rewrite [append]```."
    rewrite [append]
    rfl
  | cons head tail ih =>
    rewrite [append]
    Hint (hidden := true) "At this point, you can simplify the proof goal by using the induction
    hypothesis."
    rewrite [ih]
    rfl

TheoremTab "Word"

NewTactic induction rfl rewrite
NewDefinition Word.nil Word.cons Word.append

Conclusion "Using this lemma, you can simplify any term of the form ```word ++ nil``` to the term
```word``` in any upcoming level. Let's move on to the next proof!"
