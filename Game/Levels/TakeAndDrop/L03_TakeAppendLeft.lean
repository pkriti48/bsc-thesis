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
TheoremDoc Word.take_append_left as "take_append_left" in "Word"

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
  Hint "You should start with induction over ```word_1``` in this proof."
  induction word_1 generalizing index with
  | nil =>
    rewrite [length] at h
    Hint "Your induction hypothesis is currently ```index ≤ 0```. However, you know that index is a
    natural number, that cannot be less than 0. That means, you have to derive ```index = 0``` from
    the current expression."
    Hint (hidden := true) "You can simplify your current induction hypothesis using the theorem
    ```Nat.le_zero_eq```."
    rewrite [Nat.le_zero_eq] at h
    rewrite [h]
    rewrite [append]
    simp [take]
  | cons head tail ih =>
    Hint "At this point, you are observing the non empty case of ```word_1``` and your proof goal
    right now has two more values of an inductive type: ```word_2``` and ```index```. However, you
    do not need to observe ```word_2``` as you want to transform the left-hand side term such that
    word_2 does not occur in it anymore. So you proceed by observing all possible values of
    ```index```."
    Hint (hidden := true) "To observe all possible values of ```index```, you can either proceed
    with ```induction``` or with the ```cases``` tactic. In comparison with ```induction```,
    ```cases``` does not produce any (induction) hypothesis."
    cases index with
    | zero => simp [take]
    | succ k =>
      rewrite [length] at h
      simp [append]
      simp [take]
      Hint "The ```index``` variable in your induction hypothesis should not be
      fixed at this point. In order to have a general variable ```index```, you should have
      declared it as such when you started the induction over ```word_1```."
      apply ih
      Hint "Bring either the hypothesis ```k + 1 ≤ 1 + tail.length``` in the same form as your
      current proof goal, or vice versa."
      rewrite [<- Nat.add_comm (length tail)] at h
      Hint (hidden := true) "Now, you can transform any term of the form ```n + 1``` into
      ```succ n``` by using the theorem ```Nat.succ_eq_add_one```."
      repeat rewrite [<- Nat.succ_eq_add_one] at h
      apply Nat.le_of_succ_le_succ
      exact h

Conclusion "You just proved that the second word does not influence the result when taking a
number of characters within the bounds of the first word, allowing ```take``` to focus solely on
the first word. Well done! Let's move to the level 4!"

NewTactic cases
NewTheorem Nat.le_zero_eq Nat.succ_eq_add_one Nat.le_of_succ_le_succ
