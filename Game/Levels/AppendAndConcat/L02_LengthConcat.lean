import Game.Levels.AppendAndConcat.L01_AppendNil
namespace Word

World "AppendAndConcat"
Level 2
Title "Length of a Character Connected to a Word"

Introduction "In this level, you will prove that connecting a character ```char``` to a word
```word``` means, that the length of the obtained word is equal to 1 added to the length of
```word```."

/--
```length_concat``` proves ```length (word :: char) = length word + 1```.

Basically, the length of a word ```word :: char``` corresponds to ```one``` added to the length of
the respective ```word```.
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

TheoremTab "Nat"
TheoremTab "Word"

NewTactic apply «repeat» simp
NewTheorem add_assoc add_comm Word.length_concat
NewDefinition Word.concat Word.length

Conclusion "Well done! Next, you will prove the length of a bit more complex functions based on the
functions you encountered so far."
