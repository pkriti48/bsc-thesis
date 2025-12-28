import Game.Levels.TakeAndDrop.L05_TakeAppendRight

namespace Word

World "TakeAndDrop"
Level 6
Title "Dropping Characters Beyond the First Word in an Appended Word"

Introduction "In the last level of this world, you will prove that if ```index``` is greater
than the length of ```word_1```, then dropping ```index``` characters from ```word_1 ++
word_2``` is equivalent to dropping ```index - length word_1``` characters from ```word_2```
alone."

/--
Dropping from an appended word beyond the left operand.

If ```index``` is greater than the length of ```word_1```, then dropping ```index```
characters from ```word_1 ++ word_2``` is the same as dropping
```index - length word_1``` characters from ```word_2```.
-/
TheoremDoc Word.drop_append_right as "drop_append_right" in "Word"

Statement drop_append_right (word_1 word_2 : Word) (index : Nat) (h : length word_1 < index) :
drop (word_1 ++ word_2) index = drop word_2 (index - length word_1) := by
  induction word_1 generalizing index with
  | nil =>
    rewrite [append]
    rewrite [length]
    rewrite [Nat.sub_zero]
    rfl
  | cons head tail ih =>
    cases index with
    | zero =>
      cases h
    | succ k =>
      rewrite [append]
      simp [drop]
      rewrite [ih]
      rewrite [length]
      rewrite [<- add_comm (length tail)]
      repeat rewrite [<- Nat.succ_eq_add_one]
      rewrite [Nat.succ_sub_succ]
      rfl
      rewrite [length] at h
      rewrite [add_comm] at h
      simp at h
      exact h

Conclusion "By proving the theorem ```drop_append_right```, you showed that when dropping more
characters than the first word contains, the entire first word is removed, and the remaining
characters are taken from the second word, effectively continuing the drop into the suffix. Now,
let's move forward to the next level!"

NewTheorem Word.drop_append_right
