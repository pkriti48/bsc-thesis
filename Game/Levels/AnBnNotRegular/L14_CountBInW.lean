import Game.Levels.AnBnNotRegular.L13_CountAInW

namespace Word

World "AnBnNotRegular"
Level 14
Title "The Suffix w Contains n bs"

Introduction "Using the theorem proved in level 12, you will show that the suffix ```w```
of ```z = (u ++ v) ++ w``` contains ```n``` ```b```s."

/--
For a word $z = a^n b^n$, which is decomposed as ```z = (u ++ v) ++ w``` with
```k = length u + length v```, ```k ≤ n``` and ```length u < k```, the remaining
suffix ```w```contains exactly ```n``` replicas of ```b```.
-/
TheoremDoc Word.count_b_in_w as "count_b_in_w" in "Word"

Statement count_b_in_w (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length (u ++ v))
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.b w = n := by
  Hint "Again, you start by rewriting the word ```w``` as a sequence of ```a```s followed by a
  sequence of ```b```s and proceed accordingly thereafter."
  rewrite [w_eq_remaining_as_n_bs u v w z n k h_z z_eq h_k length_u_v_leq_n]
  rewrite [count_char_in_append]
  simp [count_char_in_replicateChar]

Conclusion "Well done! You are almost there, one more level to go to the final proof!"
