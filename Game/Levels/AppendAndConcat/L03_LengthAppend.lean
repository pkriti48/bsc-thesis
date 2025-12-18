import Game.Levels.AppendAndConcat.L02_LengthConcat
namespace Word

World "AppendAndConcat"
Level 3
Title "Length of a Word Connected to Another Word"

Introduction "In this level, you will prove the following: When the two words ```word_1``` and
```word_2``` are connected, the length of the obtained word is equal to the length of ```word_1```
added to the length of ```word_2```."

/--
```length_append``` proves ```length (word_1 ++ word_2) = length word_1 + length word_2```.

The length of any word ```word_1 ++ word_2``` can be retrieved either by calculating
```length (word_1 ++ word_2)``` or by calculating ```length word_1``` and ```length word_2``` each
individually and adding them. Both variants are equivalent to each other.
-/
TheoremDoc Word.length_append as "length_append" in "Word"

/--
Zero is the right identity of addition.

For any natural number `n`, we have `n + 0 = a`.
-/
TheoremDoc add_zero as "add_zero" in "+ and *"

/--
Zero is the left identity of addition.

For any natural number `n`, we have `0 + n = n`.
-/
TheoremDoc zero_add as "zero_add" in "+ and *"

Statement length_append (word_1 word_2 : Word) : length (word_1 ++ word_2) = length word_1 + length word_2 := by
  Hint "You should start by induction on ```word_1```."
  induction word_1 with
  | nil =>
    rewrite [append]
    rewrite [length]
    Branch
      rewrite [zero_add]
      rfl
    Hint "You can also use the ```simp``` tactic instead of```rewrite [zero_add]``` followed by ```rfl```."
    simp
  | cons head tail ih =>
    rewrite [append]
    Branch
      rewrite [length]
      rewrite [length]
    Hint "Another way to solve this proof step is to use the ```repeat``` tactic as you might have
    also done in the previous level."
    repeat rewrite [length]
    rewrite [ih]
    rewrite [<- add_assoc]
    rfl

NewTheorem add_zero zero_add Word.length_append

Conclusion "With this proof, you proved the equality of the terms ```length (word_1 ++ word_2)```
and ```length word_1 + length word_2```. From now onwards, you can rewrite both terms to one another
whenever necessary."
