import Game.MetaData
namespace Word

World "The Append and Concat World"
Level 5

Title "Length of Word Replicas"

Introduction "In this level, you will prove that replicating a word ```word``` ```n``` times
equals to a word consisting of ```n``` copies of ```word```. Thus, the length of this word is
```(length word) n```."

/--
```length_replicateChar``` proves ```length (replicateChar char n) = n```.

When a word consists of ```n``` copies of a character ```char```, then the length of such a word is
```n```.
-/
TheoremDoc lenght_replicateChar as "length_replicateChar" in "Word"

Statement length_replicateChar (char : Character) (n : Nat):
length (replicateWord word n) = (length word) * n := by
  Hint "You should start by induction on ```n```."
  induction n with
  | zero =>
    rewrite [replicateWord]
    rewrite [length]
    rewrite [Nat.mul_eq]
    rewrite [Nat.mul_zero]
    rfl
  | succ k ih =>
    rewrite [replicateWord]
    Hint "At this point, you can use the lemma ```length_append``` to simplify your current goal."
    rewrite [length_append]
    rewrite [Nat.mul_eq]
    rewrite [Nat.mul_succ]
    rewrite [ih]
    simp
    rewrite [add_comm]
    rfl

Conclusion "Hurra! You did it! You successfully proved the statements in the level 1. Let's move on
to World 2."
