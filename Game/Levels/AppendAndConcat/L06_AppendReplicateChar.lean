import Game.Levels.AppendAndConcat.L05_LengthReplicateWord

namespace Word


World "AppendAndConcat"
Level 6
Title "Appending Two Replicas of a Single Character Adds Their Counts"

Introduction "In this level, you will show that if you append two words formed by replicating
the same character — one repeated ```m``` times and the other repeated ```n``` times — the
resulting word corresponds to ```m + n``` replicas of that same character."
/--
Appending two words consisting of repeated instances of the same character.

For a character ```char``` and natural numbers ```m``` and ```n```, appending
```replicateChar char m``` with ```replicateChar char n``` produces a word
equivalent to ```replicateChar char (m + n)```.
-/
TheoremDoc Word.append_replicateChar as "append_replicateChar" in "Word"

/--
The successor of a natural number added to another number.

For any natural numbers ```a``` and ```b```, ```Nat.succ a + b``` is equal to
```Nat.succ (a + b)```. This expresses that adding ```b``` after taking the
successor of ```a``` is equivalent to taking the successor after adding ```b``` to ```a```.
-/
TheoremDoc Nat.succ_add as "Nat.succ_add" in "Nat"

Statement append_replicateChar (char : Character) (m n : Nat) :
((replicateChar char m) ++ replicateChar char n) = replicateChar char (m + n) := by
induction m with
| zero =>
  rewrite [replicateChar]
  rewrite [append]
  rewrite [zero_add]
  rfl
| succ =>
  rewrite [replicateChar]
  rewrite [append]
  rewrite [a]
  rewrite [Nat.succ_add]
  rewrite [replicateChar]
  rfl

Conclusion "You did it! You successfully resolved all proof goals in the level 1. Let's move on
to World 2."

NewTheorem Word.append_replicateChar Nat.succ_add
