import Game.Levels.AjBjNotRegular.L08_CountAInV

namespace Word


World "AjBjNotRegular"
Level 9
Title "The Middle Word v Does Not Contain any bs"

Introduction "In this level, you will show that when you decompose the word ```z = $a^n b^n$``` as
```z = (u ++ v) ++ w``` and the length of ```u ++ v``` is at most ```n```, then ```v``` is made of
only ```a```s. Following this, the count of ```b```s in ```v``` is equal to 0."

/--
If a word ```z = $a^n b^n$``` is decomposed as ```z = (u ++ v) ++ w``` and the length of ```u ++ v```
is at most ```n```, then  ```v``` consists only of ```a```s. That means, the the number of occurrences
of ```b``` in ```v``` is equal to 0.
-/
TheoremDoc Word.count_b_in_v as "count_b_in_v" in "AjBjNotRegular"

Statement count_b_in_v (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.b v = 0 := by
  rewrite [count_b_in_replicateChar_a]
  rfl
  exact Character.b
  intros char h
  apply char_elemOf_append_right (left := u) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply char_elemOf_replicateChar at h
  exact h

Conclusion "Well done! In the next level, let's move on to the next proof!"
