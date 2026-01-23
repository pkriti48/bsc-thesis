import Game.Levels.AppendAndConcat.L02_LengthConcat

namespace Word

World "AppendAndConcat"
Level 3
Title "Length of a Word Appended to Another Word"

Introduction "In this level, you will prove that the operation of appending two words adds their
lengths together. The resulting word contains exactly as many characters as the first word plus
the second."

/--
For any words ```word_1``` and ```word_2```, the length of their append
```word_1 ++ word_2``` is the sum of their lengths.
-/
TheoremDoc Word.length_append as "length_append" in "Word"

/--
Zero is the right identity of addition.

For any natural number ```n```, we have ```n + 0 = a```.
-/
TheoremDoc Nat.add_zero as "Nat.add_zero" in "Nat"

/--
Zero is the left identity of addition.

For any natural number ```n```, we have ```0 + n = n```
-/
TheoremDoc Nat.zero_add as "Nat.zero_add" in "Nat"

Statement length_append (word_1 word_2 : Word) : length (word_1 ++ word_2) = length word_1 + length word_2 := by
  Hint "In this level, you start with an induction on ```word_1``` so that you can easily prove the
  statement for all possible values of ```word_1```."
  induction word_1 with
  | nil =>
    rewrite [append]
    rewrite [length]
    Branch
      rewrite [Nat.zero_add]
      rfl
    Hint "You can also use the ```simp``` tactic to solve the current proof goal in one single step
    instead of solving it in multiple steps."
    simp
  | cons head tail ih =>
    rewrite [append]
    Branch
      rewrite [length]
      rewrite [length]
      Hint "Another way to solve this proof step is to use the ```repeat``` tactic as you might
      have also done in the previous level."
    repeat rewrite [length]
    rewrite [ih]
    rewrite [<- Nat.add_assoc]
    rfl

Conclusion "Very good! You just proved that appending words preserves all characters from both words.
Thus, the total length of the resulting word is the sum of the length of the first and the second word.
From now onwards, you can rewrite both terms to one another whenever necessary."

NewTheorem Nat.add_zero Nat.zero_add
