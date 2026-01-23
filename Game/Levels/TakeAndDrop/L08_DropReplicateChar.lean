import Game.Levels.TakeAndDrop.L07_TakeReplicateChar

namespace Word

World "TakeAndDrop"
Level 8
Title "Drop from a Sequence of Repeated Characters"

Introduction "In this level, you will prove that if you drop ```index``` characters from
```replicateChar char length```, where ```index``` does not exceed ```length```, the resulting
word consists of exactly ```length - index``` replicas of the character ```char```."

/--
For a character ```char``` and natural numbers ```length``` and ```index``` such that
```index ≤ length```, dropping ```index``` characters from ```replicateChar char length```
produces a word consisting of ```length - index``` replicas of ```char```.
-/
TheoremDoc Word.drop_replicateChar as "drop_replicateChar" in "Word"

/--
Cancel a common addend in a subtraction.

For any natural numbers ```m```, ```n```, and ```k```, adding the same number ```k``` to
both ```m``` and ```n``` does not change their difference:
```(m + k) - (n + k) = m - n```.
-/
TheoremDoc Nat.add_sub_add_right as "Nat.add_sub_add_right" in "Nat"

Statement drop_replicateChar (char : Character) (length index : Nat) (h : index ≤ length) :
drop (replicateChar char length) index = replicateChar char (length - index) := by
  Hint "The proof for ```drop_replicateChar``` is analogue to the proof for the counterpart
  ```take_replicateChar```. If you do not know how to proceed you can have a look at the
  proof for ```take_replicateChar``` in the previous level."
  induction length generalizing index with
  | zero =>
    rewrite [Nat.le_zero_eq] at h
    rewrite [h]
    rewrite [Nat.sub_zero]
    rewrite [replicateChar]
    simp [drop]
  | succ k ih =>
    cases index with
    | zero =>
      rewrite [Nat.sub_zero]
      rewrite [replicateChar]
      simp [drop]
    | succ =>
      rewrite [Nat.add_sub_add_right]
      rewrite [replicateChar]
      simp [drop]
      rewrite [ih]
      rfl
      simp at h
      exact h

Conclusion "With this, you have successfully proven all the goals of the ```Take and Drop```
World. You are getting closer to executing the pumping lemma on concrete languages. Let's move
on to the third world!"

NewTheorem Nat.add_sub_add_right
