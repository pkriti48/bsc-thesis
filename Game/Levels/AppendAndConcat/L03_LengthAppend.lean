import Game.Levels.AppendAndConcat.L02_LengthConcat

namespace Word

World "AppendAndConcat"
Level 3
Title "Length of a Word Connected to Another Word"

Introduction "In this level, you will prove the following: The operation of appending two words
adds their lengths together: the resulting word contains exactly as many characters as the first
word plus the second."

/--
The length of joining two words.

For any words `word₁` and `word₂`, the length of their append
`word₁ ++ word₂` is the sum of their lengths.
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
    Hint "You can also use the ```simp``` tactic instead of```rewrite [zero_add]``` followed by
    ```rfl```."
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
    rewrite [<- add_assoc]
    rfl

Conclusion "Very good! You just proved that appending words preserves all characters from both
operands, with the total length of the resulting word being exactly the sum of their individual
lengths. From now onwards, you can rewrite both terms to one another whenever necessary."

NewTheorem add_zero zero_add Word.length_append
