import Game.Levels.TakeAndDrop.L07_TakeReplicateChar

namespace Word

World "TakeAndDrop"
Level 8
Title "Drop from a Sequence of Repeated Characters"

Introduction "In this level, you will prove that if you drop ```index``` characters from
```replicateChar char length```, where ```index``` does not exceed ```length```, the result is
a word consisting of exactly ```length - index``` copies of the character ```char```."

/--
Dropping a prefix from a word of repeated characters.

For a character ```char``` and natural numbers ```length``` and ```index``` such that
```index ≤ length```, dropping ```index``` characters from ```replicateChar char length```
produces a word consisting of ```length - index``` copies of ```char```.
-/
TheoremDoc Word.drop_replicateChar as "drop_replicateChar" in "Word"

Statement drop_replicateChar (char : Character) (length index : Nat) (h : index ≤ length) :
drop (replicateChar char length) index = replicateChar char (length - index) := by
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

NewTheorem Word.drop_replicateChar
