import Game.Levels.AppendAndConcat.L01_AppendNil

namespace Word

World "AppendAndConcat"
Level 2

Title "Length Append"

Introduction "In this first level, you will prove the following:
  When we append the two words ```word_1``` and ```word_2```, then the length of the word we obtain
  is equal to the length of ```word_1``` and ```word_2``` added."

Statement length_append (word_1 word_2 : Word) : length (word_1 ++ word_2) = length word_1 + length word_2 := by
  Hint "You can start by induction on ```word_1```."
  induction word_1 with
  | nil =>
    rewrite [append]
    rewrite [length]
    Branch
      rewrite [add_comm]
      rewrite [add_zero]
      rfl
    Hint "You can also use the ```simp``` tactic instead of ```rewrite [add_comm]``` followed by
    ```rewrite [add_zero]```."
    simp
  | cons head tail ih =>
    rewrite [append]
    Branch
      rewrite [length]
      rewrite [length]
    Hint "Another way to solve this proof step is to use the ```repeat``` tactic. You can type
    ```repeat rewrite [length]```."
    repeat rewrite [length]
    Hint "At this point, you can rewrite the induction "
    rewrite [ih]
    rewrite [<- add_assoc]
    rfl

TacticDoc rewrite
TacticDoc rfl
TacticDoc induction

NewTactic rewrite rfl induction
NewTheorem Nat.add_assoc Nat.add_comm Nat.add_zero
NewDefinition Word.nil Word.cons Word.length Word.append

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/
