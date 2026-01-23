import Game.Levels.AjBjNotRegular.L06_CountAInU


namespace Word

World "AjBjNotRegular"
Level 7
Title "The Prefix u Does Not Contain any bs"

Introduction "In this level, you will show that when you decompose the word ```z = $a^n b^n$``` as
```z = (u ++ v) ++ w``` and the length of ```u ++ v``` is at most ```n```, then ```u``` is made of
only ```a```s. Following this, the count of ```b```s in ```u``` is equal to 0."

/--
If a word ```z = $a^n b^n$``` is decomposed as ```z = (u ++ v) ++ w``` and the length of ```u ++ v```
is at most ```n```, then  ```u``` consists only of ```a```s. That means, the the number of occurrences
of ```b``` in ```u``` is equal to 0.
-/
TheoremDoc Word.count_b_in_u as "count_b_in_u" in "AnBnNotRegular"

Statement count_b_in_u (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.b u = 0 := by
  rewrite [count_b_in_replicateChar_a]
  rfl
  exact Character.b
  intros char h
  apply char_elemOf_append_left (right := v) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply char_elemOf_replicateChar at h
  exact h

Conclusion "Very good! In the next level, you will show that ```v``` consists of as many ```a```s as
the length of ```v``` is."
