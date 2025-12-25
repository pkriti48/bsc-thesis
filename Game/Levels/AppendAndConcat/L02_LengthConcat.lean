import Game.Levels.AppendAndConcat.L01_AppendNil

namespace Word

World "AppendAndConcat"
Level 2
Title "Prepending a Character Increases Word Length by One"

Introduction "In this level, you will prove that concatenating a character ```char``` to the
end of a ```word``` increases its length by one.

Specifically, the length of word :: char is equal to the length of word plus one.
"

/--
The length of a word after concatenating a character is the length of the word plus one.

For any ```word``` and character ```char```, ```length (concat word char) = length word + 1```.
This reflects the fact that concatenating a character to a word increases its length by one.
-/
TheoremDoc Word.length_concat as "length_concat" in "Word"

/--
Addition is associative.

For all natural numbers `n`, `m`, and `k`, we have
`(n + m) + k = n + (m + k)`.
-/
TheoremDoc add_assoc as "add_assoc" in "+ and *"

/--
Addition is commutative.

For all natural numbers `n` and `m`, we have `n + m = n + m`.
-/
TheoremDoc add_comm as "add_comm" in "+ and *"

Statement length_concat (word : Word) (char : Character) : length (word :: char) = length word + 1 := by
  Hint "You should start by induction on ```word```."
  induction word with
  | nil =>
    rewrite [concat]
    Branch
      rewrite [length]
      rewrite [length]
      rewrite [length]
      Hint (hidden := true) "You can also solve this step by using the ```repeat``` tactic. You can
      execute ```repeat rewrite [length]```."
    repeat rewrite [length]
    Hint "Lean is very precise, so you cannot use the ```rfl``` tactic yet. To retrieve the
    equality between the expressions on both sides of the ```=``` sign, you have to use the
    commutative property of the mathematical addition."
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

Conclusion "Well done! You just demonstrated that extending a word by one character results in
a word whose length is precisely one greater than before. Let's move on to the next proof!"

NewTactic apply «repeat» simp
NewTheorem add_assoc add_comm Word.length_concat
NewDefinition Word.concat Word.length
