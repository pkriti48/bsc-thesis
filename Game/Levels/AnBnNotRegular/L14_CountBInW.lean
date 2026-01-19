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
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k) :
countCharInWord Character.b w = n := by
  rewrite [w_eq_remaining_as_n_bs u v w z n k h_z z_eq h_k k_leq_n length_u_lt_k]
  rewrite [count_char_in_append]
  simp [count_char_in_replicateChar]

Conclusion "Well done! You are almost there, one more level to go to the final proof!"
