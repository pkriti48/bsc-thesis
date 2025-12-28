import Game.Levels.AppendAndConcat.L06_AppendReplicateChar

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
  Hint "You should start by induction on ```word```."
  induction word with
  | nil =>
    rewrite [length]
    Branch
      rewrite [take]
      rfl
    simp [take]
  | cons head tail ih =>
    rewrite [length]
    simp [take]
    exact ih

Conclusion "You did it! You just showed that if you use the ```take``` function with the full
length of a word, no characters are omitted, and the resulting word is exactly the same as the
original. Let's move on to the next proof!"

NewTactic exact
NewTheorem Word.take_all
NewDefinition Word.take
