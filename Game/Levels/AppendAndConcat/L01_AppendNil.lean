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
  Hint "You should start with induction on ```word``` so that you can prove the statement for the
  empty word ```nil``` and for any non-empty word ```cons head tail```, where the non-empty word
  corresponds to a character (```head```) prepended to a word (```tail```)."
  induction word with
  | nil =>
    Hint "So far, you have seen how an expression can be simplified using the ```rewrite``` tactic
    and a theorem if you have played the Natural Number Game. Now, you will see that you can
    combine this tactic also with function definitions: You can simplify your current proof state
    ```nil ++ nil = nil``` by executing the tactic ```rewrite [append]```, as it corresponds to
    appending an empty word ```nil``` with another empty word ```nil```. The result is then the
    equation ```nil = nil```."
    rewrite [append]
    Hint "If you do not know how to proceed, click on the ```Show more help!``` button!"
    Hint (hidden := true) "In order to prove this proof goal, you can execute the ```rfl``` tactic."
    rfl
  | cons head tail ih =>
    Hint "As you did in the first proof goal, you can start with rewriting the ```append```
    function. This rewrites the term on the left-hand side of the ```=``` sign into ```cons head
    (tail ++ nil)."
    rewrite [append]
    Hint "At this point, you can simplify the proof goal by using the induction hypothesis, as
    you would do in any proof by induction for the non-base case. For that, you have two
    possibilities to proceed from this step. You can either proceed by executing the ```simp```
    tactic followed by ```exact``` tactic combined with the induction hypothesis or you rewrite
    the induction hypothesis and then execute ```rfl```."
    Hint "The ```simp``` tactic simplifies your current proof goal using all function definitions
    and theorems that are currently available and have been notated with the ```simp``` keyword.
    And, the ```exact``` tactic can be applied to a proof goal that matches with an induction
    hypothesis character by character."
    Branch
      simp
      exact ih
    rewrite [ih]
    rfl

Conclusion "```append_nil``` establishes that the empty word acts as a neutral element for word
appending: adding it to the end of any word leaves the word unchanged. Using this lemma, you
can simplify any term of the form ```word ++ nil``` to the term ```word``` in any upcoming
level. Let's move on to the next proof!"

NewTactic exact induction rfl rewrite simp
NewDefinition Word.nil Word.cons Word.append
