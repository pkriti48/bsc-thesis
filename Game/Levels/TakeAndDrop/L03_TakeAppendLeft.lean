import Game.Levels.TakeAndDrop.L02_DropAll

namespace Word

World "TakeAndDrop"
Level 3
Title "Taking Characters Within the First Word of an Appended Word"

Introduction "In this level, you will prove that if the number of characters ```index``` to take
does not exceed the length of the first word ```word_1```, then taking ```index``` characters
from ```word_1 ++ word_2``` is equivalent to taking ```index``` characters from ```word_1```
alone. The second word ```word_2``` has no effect in this case."

/--
Taking from an appended word within the left operand.

If the number of characters taken does not exceed the length of ```word_1```,
then taking ```index``` characters from ```word_1 ++ word_2``` is the same as taking
```index``` characters from ```word_1``` alone.
-/
TheoremDoc Word.take_append_left as "take_append" in "Word"

/--
The successor of a natural number is adding one.

For any natural number ```n```, ```Nat.succ n``` is equal to ```n + 1```.
-/
TheoremDoc Nat.succ_eq_add_one as "Nat.succ_eq_add_one" in "Nat"

/--
A natural number less than or equal to zero is zero.

If ```n ≤ 0```, then ```n = 0```.
-/
TheoremDoc Nat.le_zero_eq as "Nat.le_zero_eq" in "Nat"

/--
Cancel successors from both sides of an inequality.

If ```Nat.succ a ≤ Nat.succ b```, then ```a ≤ b```.
-/
TheoremDoc Nat.le_of_succ_le_succ as "Nat.le_of_succ_le_succ" in "Nat"

Statement take_append_left (word_1 word_2 : Word) (index : Nat) (h : index ≤ (length word_1)) :
take (word_1 ++ word_2) index = take word_1 index := by
  induction word_1 generalizing index with
  | nil =>
    rewrite [length] at h
    rewrite [Nat.le_zero_eq] at h
    rewrite [h]
    rewrite [append]
    simp [take]
  | cons head tail ih =>
    cases index with
    | zero => simp [take]
    | succ k =>
      rewrite [length] at h
      simp [append]
      simp [take]
      Hint (hidden := true) "The ```index``` variable in your induction hypothesis should not be
      fixed at this point. In order to have a general variable ```index```, you should have
      declared it as such when you started the induction over ```word_1```."
      apply ih
      Hint "Bring either the hypothesis ```k + 1 ≤ 1 + tail.length``` in the same form as your
      current proof goal, or vice versa."
      rewrite [<- add_comm (length tail)] at h
      Hint (hidden := true) "At this point, you can transform any term of the form ```n + 1``` into
      ```succ n``` by using the theorem ```Nat.succ_eq_add_one```."
      repeat rewrite [<- Nat.succ_eq_add_one] at h
      apply Nat.le_of_succ_le_succ
      exact h

Conclusion "You just proved that the second word does not influence the result when taking a
number of characters within the bounds of the first word, allowing ```take``` to focus solely on
the first word. Well done! Let's move to the level 4!"

NewTactic cases
NewTheorem Nat.le_zero_eq Nat.succ_eq_add_one Nat.le_of_succ_le_succ
