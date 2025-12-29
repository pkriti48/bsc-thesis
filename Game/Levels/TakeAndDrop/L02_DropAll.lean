import Game.Levels.TakeAndDrop.L01_TakeAll

namespace Word

World "TakeAndDrop"
Level 2
Title "Drop All Characters of a Word"

Introduction "In this level, you will prove the theorem ```drop_all```. It states that dropping
a number of characters equal to the length of a word results in the empty word ```nil```."

/--
Dropping the full length of a word yields the empty word.

For any word ```word```, dropping ```length word``` characters removes all
characters, resulting in the empty word.
-/
TheoremDoc Word.drop_all as "drop_all" in "Word"

Statement drop_all (word : Word) : drop word (length word) = nil := by
  induction word with
  | nil =>
    rewrite [drop]
    rfl
  | cons head tail ih =>
    rewrite [length]
    simp [drop]
    rewrite [ih]
    rfl

Conclusion "Well done! You just proved that using the ```drop``` function with the full length
of a word removes all characters, leaving no remaining characters. Let's move forward!"

NewDefinition Word.drop
