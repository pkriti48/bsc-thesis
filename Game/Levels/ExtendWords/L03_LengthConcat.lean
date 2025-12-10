import Game.MetaData
namespace Word

World "The Append and Concat World"
Level 3

Title "Length Concat"

Introduction "In this level, you will prove the following:
  When we concatenate a character ```char``` to a word ```word```, then the length of the word we obtain
  is equal to 1 added to the length of ```word```."

/--
```length_concat``` proves length (word :: char) = length word + 1.

Basically, the length of a word ```word :: char``` corresponds to ```one``` added to the length of
the respective word.
-/
TheoremDoc lenght_concat as "length_concat" in "Word"

Statement length_concat (word : Word) (char : Character) : length (word :: char) = length word + 1 := by
  Hint "You should start by induction on ```word```."
  induction word with
  | nil =>
    rewrite [concat]
    Branch
      rewrite [length]
      rewrite [length]
      rewrite [length]
    Hint "Another way to solve this proof step is to use the ```repeat``` tactic as you might have
    also done in the previous level."
    repeat rewrite [length]
    Hint "Lean is very precise, so you cannot use the ```rfl``` tactic at this point yet. To make the
    expressions equal on both sides of the ```=``` sign, you have to use the commutative
    property of the mathematical addition."
    Branch
      apply add_comm
    rewrite [add_comm]
    rfl
  | cons head tail ih =>
    rewrite [concat]
    repeat rewrite [length]
    rewrite [ih]
    rewrite [add_assoc]
    rfl

Conclusion "Well done! Now, let's move on to proving the length of a bit more complex functions
based on the functions you encountered so far."
