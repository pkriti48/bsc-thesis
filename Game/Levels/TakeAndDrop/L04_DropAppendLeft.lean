import Game.Levels.TakeAndDrop.L03_TakeAppendLeft

namespace Word

World "TakeAndDrop"
Level 4
Title "Dropping Characters Within the First Word of an Appended Word"

Introduction "In this level, you will prove that if the number of characters to drop ```index```
does not exceed the length of the first word ```word_1```, then dropping ```index``` characters
from ```word_1 ++ word_2``` is equivalent to dropping ```index``` characters from ```word_1```
and then appending the second word ```word_2```."

/--
Dropping from an appended word within the left operand.

If the number of characters dropped does not exceed the length of ```word_1```,
then dropping ```index``` characters from ```word_1 ++ word_2``` is the same as
dropping ```index``` characters from ```word_1``` and then appending ```word_2```.
-/
TheoremDoc Word.drop_append_left as "drop_append_left" in "Word"

Statement drop_append_left (word_1 word_2 : Word) (index : Nat) (h: index ≤ length word_1) :
drop (word_1 ++ word_2) index = (drop word_1 index) ++ word_2 := by
  induction word_1 generalizing index with
  | nil =>
    rewrite [length, Nat.le_zero_eq] at h
    rewrite [h, append]
    simp [drop]
    rewrite [append]
    induction word_2 with
    | nil => simp [drop]
    | cons head tail ih => simp [drop]
  | cons head tail ih =>
    rewrite [append]
    cases index with
    | zero =>
      simp [drop]
      rewrite [append]
      rfl
    | succ k =>
      simp [drop]
      rewrite [ih]
      rfl
      rewrite [length] at h
      rewrite [<- add_comm (length tail)] at h
      rewrite [<- Nat.succ_eq_add_one k, <- Nat.succ_eq_add_one (length tail)] at h
      simp at h
      exact h

Conclusion "Very good! You just proved that dropping characters in ```word_1``` and then
appending ```word_2``` leaves ```word_2``` unaffected. Let's move on to proving the corresponding
theorems for take and drop for ```index ≥ length word_1```."

NewTactic cases
NewTheorem Word.drop_append_left
