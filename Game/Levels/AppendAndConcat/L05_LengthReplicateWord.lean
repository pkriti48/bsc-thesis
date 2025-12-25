import Game.Levels.AppendAndConcat.L04_LengthReplicateChar

namespace Word


World "AppendAndConcat"
Level 5
Title "Length of Word Replicas"

Introduction "In this level, you will show how the length of a word changes when it is repeated
multiple times using the ```replicateWord``` function. It states that if a word is repeated
```n``` times, the length of the resulting word is equal to ```n``` multiplied by the length of
the original word, reflecting the additive effect of appending the same word repeatedly."

/--
The length of a word repeated multiple times.

For any word `word` and natural number `n`, `replicateWord word n`
produces a word consisting of `n` copies of `word` appended together.
The length of this resulting word is `n` times the length of `word`.
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
    rewrite [Nat.mul_zero]
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

Conclusion "You did it! You successfully resolved all proof goals in the level 1. Let's move on
to World 2."

NewTheorem Word.length_replicateWord Nat.mul_zero Nat.mul_succ
NewDefinition Word.replicateWord
