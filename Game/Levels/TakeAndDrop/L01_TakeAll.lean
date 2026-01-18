import Game.Levels.AppendAndConcat

namespace Word

World "TakeAndDrop"
Level 1
Title "Take All Characters of a Word"

Introduction "In this level, you will provef: This theorem states that taking a number of
characters equal to the length of a word returns the word itself."

/--
Taking the full length of a word returns the word itself.

For any word ```word```, taking ```length word``` characters yields the original
word unchanged.
-/
TheoremDoc Word.take_all as "take_all" in "Word"

Statement take_all (word : Word) : take word (length word) = word := by
  induction word with
  | nil =>
    rewrite [length]
    Branch
      rewrite [take]
      rfl
    Hint ""
    rewrite [take]
    rfl
  | cons head tail ih =>
    rewrite [length]
    Hint "In order to solve the current goal, the easiest way to proceed is to execute
    ```simp [take]```. As described earlier, the ```simp``` tactic simplifies your current proof
    goal using all function definitions and theorems that are curently available and have been
    notated with the ```simp``` keyword. In this case, it additionally uses the ```take``` function
    to simplify the current proof goal further."
    simp [take]
    exact ih

Conclusion "You did it! You just showed that if you use the ```take``` function with the full
length of a word, no characters are omitted, and the resulting word is exactly the same as the
original. Let's move on to the next proof!"

NewDefinition Word.take
