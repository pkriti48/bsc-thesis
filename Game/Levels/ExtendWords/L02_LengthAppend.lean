import Game.MetaData

namespace Word

World "The Append and Concat World"
Level 2

Title "Length Append"

Introduction "In this first level, you will prove the following:
  When we append the two words ```word_1``` and ```word_2```, then the length of the word we obtain
  is equal to the length of ```word_1``` and ```word_2``` added."

Statement length_append (word_1 word_2 : Word) : length (word_1 ++ word_2) = length word_1 + length word_2 := by
  Hint "You should start by induction on ```word_1```."
  induction word_1 with
  | nil =>
    rewrite [append]
    rewrite [length]
    Branch
      Branch
        rewrite [zero_add]
        rfl
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
    Hint "At this point, you can rewrite your proof goal into the induction hypothesis."
    rewrite [ih]
    rewrite [<- add_assoc]
    rfl

TacticDoc «repeat»
TacticDoc rewrite
TacticDoc rfl
TacticDoc induction

NewTactic «repeat» rewrite rfl induction
NewTheorem add_assoc add_comm add_zero zero_add
NewDefinition Word.nil Word.cons Word.length Word.append

Conclusion "From now on, you can use the lemma ```length_append``` to prove the goals in the upcoming levels."

/- Use these commands to add items to the game's inventory. -/
