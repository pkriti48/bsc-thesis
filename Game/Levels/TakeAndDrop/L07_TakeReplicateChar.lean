import Game.Levels.TakeAndDrop.L06_DropAppendRight

namespace Word

World "TakeAndDrop"
Level 7
Title "Take from a Sequence of Repeated Characters"

Introduction "In this level, you will prove that if you take ```index``` characters from
```replicateChar char length```, where ```index``` does not exceed ```length```, the resulting
word consists of exactly ```index``` replicas of the character ```char```."

/--
For a character ```char``` and natural numbers ```length``` and ```index``` such that
```index ≤ length```, taking ```index``` characters from ```replicateChar char length```
produces a word consisting of ```index``` replicas of ```char```.
-/
TheoremDoc Word.take_replicateChar as "take_replicateChar" in "Word"

Statement take_replicateChar (char : Character) (length index : Nat) (h : index ≤ length) :
take (replicateChar char length) index = replicateChar char index := by
  induction length generalizing index with
  | zero =>
    Hint "As already discussed earlier, ```index``` is a natural number so it cannot be 0. Thus, it has to
    be 0 when ```index ≤ length``` and ```length = 0```."
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
      Hint "As you can see, your current proof goal and the hypothesis ```h``` represent a very
      similar fact. You can now either transform ```h``` such that it is equal to the current proof
      goal or vice versa."
      Branch
        repeat rewrite [<- Nat.succ_eq_add_one] at h
        apply Nat.le_of_succ_le_succ at h
      apply Nat.le_of_succ_le_succ
      repeat rewrite [Nat.succ_eq_add_one]
      exact h

Conclusion "Well done! Now, let's go forward and prove the counterpart of this theorem, which is
the theorem ```drop_replicateChar```."
