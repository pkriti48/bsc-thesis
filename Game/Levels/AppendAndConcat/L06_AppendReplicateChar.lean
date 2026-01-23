import Game.Levels.AppendAndConcat.L05_LengthReplicateWord

namespace Word


World "AppendAndConcat"
Level 6
Title "Appending Two Replicas of a Single Character Adds Their Counts"

Introduction "In this level, you will show that if you append a word consisting of ```n``` replicas
of a character to a word consisting ```m``` replicas of the same character, then the resulting word
corresponds to ```m + n``` replicas of that character."

/--
For a character ```char``` and natural numbers ```m``` and ```n```, appending
```replicateChar char n``` to ```replicateChar char m``` produces a word
equivalent to ```replicateChar char (m + n)```.
-/
TheoremDoc Word.append_replicateChar as "append_replicateChar" in "Word"

/--
The successor of a natural number added to another number.

For any natural numbers ```a``` and ```b```, ```Nat.succ a + b``` is equal to
```Nat.succ (a + b)```.
-/
TheoremDoc Nat.succ_add as "Nat.succ_add" in "Nat"

Statement append_replicateChar (char : Character) (m n : Nat) :
((replicateChar char m) ++ replicateChar char n) = replicateChar char (m + n) := by
Hint "You can start with an induction on ```m```, as it is mostly easier to proceed from left to right."
induction m with
| zero =>
  rewrite [replicateChar]
  rewrite [append]
  rewrite [Nat.zero_add]
  rfl
| succ k ih =>
  rewrite [replicateChar]
  rewrite [append]
  rewrite [ih]
  Hint "To reach an equality between the terms on both sides of the ```=``` sign, start by
  transforming ```replicateChar char (k + 1 + n)``` to an expression which can be easily
  processed further."
  rewrite [Nat.succ_add]
  Hint (hidden := true) "Now, you can rewrite the term on the right using ```replicateChar```."
  rewrite [replicateChar]
  rfl

Conclusion "You did it! You successfully resolved all proof goals in the level 1. Let's move on
to World 2."

NewTheorem Nat.succ_add
