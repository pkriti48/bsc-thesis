import Game.Levels.AppendAndConcat.L04_LengthReplicateChar
namespace Word


World "AppendAndConcat"
Level 5
Title "Length of Word Replicas"

Introduction "In this level, you will prove that replicating a word ```word``` ```n``` times
equals to a word consisting of ```n``` copies of ```word```. Thus, the length of this word is
```(length word) n```."

/--
```length_replicateWord``` proves ```length (replicateWord word n) =  (length word) * n```.

If a word consists of ```n``` copies of a word ```word``` the length of such a word is
```(length word) * n```.
-/
TheoremDoc Word.length_replicateWord as "length_replicateWord" in "Word"

/--
Zero is an absorbing element for multiplication.

For any natural number `n`, we have `n * 0 = 0`.
-/
TheoremDoc Nat.mul_zero as "Nat.mul_zero" in "+ and *"

/--
Multiplication by a successor.

For any natural numbers `n` and `m`, multiplying `n` by `Nat.succ m`
is equal to adding `n` to `n * m`.
-/
TheoremDoc Nat.mul_succ as "Nat.mul_succ" in "+ and *"

Statement length_replicateWord (word : Word) (n : Nat):
length (replicateWord word n) = (length word) * n := by
  Hint "You should start by induction on ```n```."
  induction n with
  | zero =>
    rewrite [replicateWord]
    rewrite [length]
    rewrite [mul_zero]
    rfl
  | succ k ih =>
    rewrite [replicateWord]
    Hint "At this point, you can use the lemma ```length_append```, you proved in Level 3, to
    simplify your current goal."
    rewrite [length_append]
    rewrite [Nat.mul_succ]
    rewrite [ih]
    rewrite [add_comm]
    rfl

NewTheorem Word.length_replicateWord Nat.mul_zero Nat.mul_succ
NewDefinition Word.replicateWord

Conclusion "You did it! You successfully proved the statements in the level 1. Let's move on to
World 2."
