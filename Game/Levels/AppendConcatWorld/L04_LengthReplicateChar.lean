import Game.MetaData
namespace Word

World "The Append and Concat World"
Level 4

Title "Length of Character Replicas"

Introduction "In this level, you will prove that replicating a character ```char``` ```n``` times
equals to a word consisting of ```n``` copies of ```char```. Thus, the length of this word is ```n```."

/--
```length_replicateChar``` proves ```length (replicateChar char n) = n```.

When a word consists of ```n``` copies of a character ```char```, then the length of such a word is
```n```.
-/
TheoremDoc lenght_replicateChar as "length_replicateChar" in "Word"

Statement length_replicateChar (char : Character) (n : Nat): length (replicateChar char n) = n := by
  Hint "You should start by induction on ```n```."
  induction n with
  | zero =>
    Hint "At this point, you can ```rewrite replicatChar```."
    rewrite [replicateChar]
    rewrite [length]
    rfl
  | succ k ih =>
    rewrite [replicateChar]
    rewrite [length]
    rewrite [ih]
    rewrite [add_comm]
    rfl

Conclusion "Very good! Let's move forward to the next and last proof of the first world."
