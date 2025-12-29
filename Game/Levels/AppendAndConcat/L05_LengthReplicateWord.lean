import Game.Levels.AppendAndConcat.L04_LengthReplicateChar

namespace Word


World "AppendAndConcat"
Level 5
Title "Length of Word Replicas"

Introduction "In this level, you will showthat if a word is repeated ```n``` times, the length
of the resulting word is equal to ```n``` multiplied by the length of the original word,
reflecting the additive effect of appending the same word repeatedly."

/--
The length of a word repeated multiple times.

For any word ```word``` and natural number ```n```, ```replicateWord word n```
produces a word consisting of ```n``` copies of ```word``` appended together.
The length of this resulting word is ```n``` times the length of ```word```.
-/
TheoremDoc Word.length_replicateWord as "length_replicateWord" in "Word"

/--
Zero is an absorbing element for multiplication.

For any natural number ```n```, we have ```n * 0 = 0```.
-/
TheoremDoc Nat.mul_zero as "Nat.mul_zero" in "Nat"

/--
Multiplication by a successor.

For any natural numbers ```n``` and ```m```, multiplying ```n``` by ```Nat.succ m```
is equal to adding ```n``` to ```n * m```.
-/
TheoremDoc Nat.mul_succ as "Nat.mul_succ" in "Nat"

Statement length_replicateWord (word : Word) (n : Nat):
length (replicateWord word n) = (length word) * n := by
  Hint (hidden := true) "You should start by induction on ```n``` as you did in the previous level."
  induction n with
  | zero =>
    rewrite [replicateWord]
    rewrite [length]
    Branch
      Hint "To reach an equality on both sides, you have to retrieve ```0``` on the right hand side
      of the ```=``` sign. You can do that by using the ```Nat.mul_zero``` theorem."
      rewrite [Nat.mul_zero]
      rfl
    simp
  | succ k ih =>
    rewrite [replicateWord]
    Hint "Here, you can use the ```length_append``` theorem, you proved in Level 3, to
    simplify your current goal."
    rewrite [length_append]
    Hint "Similar to simplifying by using ```Nat.mul_zero``` in the ```nil``` case, you can use
    ```Nat.mul_succ``` here."
    rewrite [Nat.mul_succ]
    rewrite [ih]
    rewrite [add_comm]
    rfl

Conclusion "By proving the theorem ```length_replicateWord```, you confirmed that repeating a
word ```n``` times produces a word whose length is exactly ```n``` times the length of the
original word. Now, let's go over to the last level of this world!"

NewTheorem Word.length_replicateWord Nat.mul_zero Nat.mul_succ
NewDefinition Word.replicateWord
