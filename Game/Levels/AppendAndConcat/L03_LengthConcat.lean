import Game.Levels.AppendAndConcat.L02_LengthAppend
namespace Word

World "AppendAndConcat"
Level 3

Title "Length Concat"

Introduction "In this level, you will prove the following:
  When we concatenate a character ```char``` to a word ```word```, then the length of the word we obtain
  is equal to 1 added to the length of ```word```."

Statement length_concat (word : Word) (char : Character) : length (word :: char) = length word + 1 := by
  Hint "You can start by induction on ```word```."
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
    rewrite [ih, add_assoc]
    rfl

NewTactic rewrite rfl induction
NewTheorem add_comm add_assoc
NewDefinition Word.concat

Conclusion "This last message appears if the level is solved."
