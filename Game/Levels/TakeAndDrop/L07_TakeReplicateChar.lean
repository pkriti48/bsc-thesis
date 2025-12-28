import Game.Levels.TakeAndDrop.L06_DropAppendRight

namespace Word

World "TakeAndDrop"
Level 7
Title "Take from a Sequence of Repeated Characters"

Introduction "In this level, you will prove that if you take ```index``` characters from
```replicateChar char length```, where ```index``` does not exceed ```length```, the result is
a word consisting of exactly ```index``` copies of the character ```char```."

/--
Taking a prefix of repeated characters.

For a character ```char``` and natural numbers ```length``` and ```index``` such that
```index ≤ length```, taking ```index``` characters from ```replicateChar char length```
produces a word consisting of ```index``` copies of ```char```.
-/
TheoremDoc Word.take_replicateChar as "take_replicateChar" in "Word"


Statement take_replicateChar (char : Character) (length index : Nat) (h : index ≤ length) :
take (replicateChar char length) index = replicateChar char index := by
  induction length generalizing index with
  | zero =>
    rewrite [Nat.le_zero_eq] at h
    rewrite [h]
    rewrite [replicateChar]
    rfl
  | succ n ih =>
    cases index with
    | zero =>
      rewrite [replicateChar]
      simp [take]
    | succ =>
      repeat rewrite [replicateChar]
      simp [take]
      apply ih
      apply Nat.le_of_succ_le_succ
      rewrite [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      exact h

Conclusion "Well done! Now, let's go forward and prove the counterpart of this theorem, which is
the theorem ```drop_replicateChar```."

NewTheorem Word.take_replicateChar
