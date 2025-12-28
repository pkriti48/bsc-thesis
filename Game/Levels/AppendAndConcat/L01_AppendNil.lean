import Game.Metadata

namespace Word

World "AppendAndConcat"
Level 1
Title "Appending an Empty Word Preserves the Original Word"

Introduction "You will start playing the game by proving that appending the empty word
```nil``` to any ```word``` leaves ```word``` unchanged.

Basically, the theorem ```append_nil``` states the identity property of nil in word concatenation.
"

/--
Appending the empty word ```nil``` to any word results in the word itself.

For any word ```word```, ```word ++ nil = word```. This reflects the identity
property of the empty word in word concatenation.
-/
TheoremDoc Word.append_nil as "append_nil" in "Word"

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

Conclusion "```append_nil``` establishes that the empty word acts as a neutral element for word
appending: adding it to the end of any word leaves the word unchanged. Using this lemma, you
can simplify any term of the form ```word ++ nil``` to the term ```word``` in any upcoming
level. Let's move on to the next proof!"

NewTactic induction rfl rewrite
NewTheorem Word.append_nil
NewDefinition Word.nil Word.cons Word.append
