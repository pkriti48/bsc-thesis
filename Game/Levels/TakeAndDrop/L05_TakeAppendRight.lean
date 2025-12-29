import Game.Levels.TakeAndDrop.L04_DropAppendLeft

namespace Word

World "TakeAndDrop"
Level 5
Title "Taking Characters Beyond the First Word in an Appended Word"

Introduction "The following theorem ```take_append_right``` states that if ```index``` is
greater than the length of ```word_1```, then taking ```index``` characters from ```word_1 ++
word_2``` results in all of word₁ followed by the first ```index - length word_1``` characters
of ```word_2```."

/--
Taking from an appended word beyond the left operand.

If ```index``` is greater than the length of ```word_1```, then taking ```index```
characters from ```word_1 ++ word_2``` yields all of ```word_1``` followed by the
remaining characters taken from ```word_2```.
-/
TheoremDoc Word.take_append_right as "take_append_right" in "Word"

/--
Subtracting zero from a natural number.

For any natural number ```n```, we have ```n - 0 = n```.
-/
TheoremDoc Nat.sub_zero as "Nat.sub_zero" in "Nat"

/--
Subtracting successors cancels on both sides.

For any natural numbers ```a``` and ```b```, subtracting ```Nat.succ b``` from
```Nat.succ a``` is the same as subtracting ```b``` from ```a```.
-/
TheoremDoc Nat.succ_sub_succ as "Nat.succ_sub_succ" in "Nat"

Statement take_append_right (word_1 word_2 : Word) (index : Nat) (h : length word_1 < index) :
take (word_1 ++ word_2) index = word_1 ++ (take word_2 (index - length word_1)) := by
  induction word_1 generalizing index with
  | nil =>
    rewrite [length]
    repeat rewrite [append]
    rewrite [Nat.sub_zero]
    rfl
  | cons head tail ih =>
    cases index with
    | zero => cases h
    | succ k =>
      repeat rewrite [append]
      simp [take]
      rewrite [ih]
      rewrite [length]
      rewrite [<- add_comm (length tail)]
      repeat rewrite [<- Nat.succ_eq_add_one]
      Hint "In order to bring the term on the left hand side of the ```=``` sign, you can cancel the
      successors of both ```k``` and ```length tail``` by subtracting ```succ (length tail)``` from
      ```succ k```."
      rewrite [Nat.succ_sub_succ]
      rfl
      rewrite [length] at h
      rewrite [add_comm] at h
      simp at h
      exact h

Conclusion "Well done! You just showed that ```take_append_right``` shows that when taking more
characters than are present in the first word, the result includes the entirety of the first
word plus the corresponding number of characters from the second word, correctly spanning the
boundary between the two. Let's move on to the last proof in the second world."

NewTheorem Nat.sub_zero Nat.succ_sub_succ Word.take_append_right
