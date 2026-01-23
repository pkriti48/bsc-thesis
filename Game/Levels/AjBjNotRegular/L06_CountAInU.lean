import Game.Levels.AjBjNotRegular.L05_LeftEqReplicateCharA

namespace Word

World "AjBjNotRegular"
Level 6
Title "The Prefix u Consists Only of as"

Introduction "In this level, you will show that when you decompose the word ```z = $a^n b^n$``` as
```z = (u ++ v) ++ w``` and the length of ```u ++ v``` is at most ```n```, then ```u``` is made of
only ```a```s. Following this, the count of ```a```s in ```u``` is equal to the length of ```u```."

/--
If a word ```z = $a^n b^n$``` is decomposed as ```z = (u ++ v) ++ w``` and the length of ```u ++ v```
is at most ```n```, then  ```u``` consists only of ```a```s. That means, the the number of occurrences
of ```a``` in ```u``` is equal to the length of ```u```.
-/
TheoremDoc Word.count_a_in_u as "count_a_in_u" in "AnBnNotRegular"

Statement count_a_in_u (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.a u = length u := by
  apply count_a_in_replicateChar_a
  exact Character.a
  Hint "As you did earlier, you can split this implication into an hypothesis and proof goal using
  the ```intros``` tactic."
  intros char h
  apply char_elemOf_append_left (right := v ) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply char_elemOf_replicateChar at h
  exact h

Conclusion "Well done! Next, you will show, how man ```b```s occur in the word ```u```."

