import Game.MetaData

namespace Word

World "The Append and Concat World"
Level 2

Title "Length of Two Appended Words"

Introduction "In this level, you will prove the following: When the two words ```word_1``` and
```word_2``` are appended, the length of the word obtained is equal to the length of ```word_1``` and
```word_2``` added together."

/--
```length_append``` proves ```length (word_1 ++ word_2) = length word_1 + length word_2```.

Basically, to retrieve the length of any word ```word_1 ++ word_2``` either by calculating
```length (word_1 ++ word_2)``` or by calculating ```length word_1``` and ```length word_2```
individually and add them. Both variants are equivalent to each other.
-/
TheoremDoc length_append as "length_append" in "Word"

Statement length_append (word_1 word_2 : Word) : length (word_1 ++ word_2) = length word_1 + length word_2 := by
  Hint "You should start by induction on ```word_1```."
  induction word_1 with
  | nil =>
    rewrite [append]
    rewrite [length]
    Branch
      rewrite [zero_add]
      rfl
    Hint "You can also use ```simp``` instead of ```rewrite [zero_add]``` followed by ```rfl```."
    simp
  | cons head tail ih =>
    rewrite [append]
    Branch
      rewrite [length]
      rewrite [length]
    Hint "You can also solve this step by using the ```repeat``` tactic. You can execute
    ```repeat rewrite [length]```."
    repeat rewrite [length]
    rewrite [ih]
    rewrite [<- add_assoc]
    rfl

TheoremTab "Word"

NewTactic «repeat» simp
NewDefinition Word.length zero_add add_assoc

Conclusion "With this proof, you proved the equality of the terms ```length (word_1 ++ word_2)```
and ```length word_1 + length word_2```. From now onwards, you can rewrite both terms to one another
whenever necessary."

/- Use these commands to add items to the game's inventory. -/
