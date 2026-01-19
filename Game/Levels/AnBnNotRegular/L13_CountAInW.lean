import Game.Levels.AnBnNotRegular.L12_WEqRemainingAsNBs

namespace Word

World "AnBnNotRegular"
Level 13
Title "The Suffix w Contains (n - k) as"

Introduction "Using the theorem proved in the previous level, you will show that the suffix ```w```
of ```z = (u ++ v) ++ w``` contains ```n - k``` ```a```s."

/--
For a word $z = a^n b^n$, which is decomposed as ```z = (u ++ v) ++ w``` with
```k = length u + length v```, ```k ≤ n``` and ```length u < k```, the remaining
suffix ```w```contains exactly ```n - k``` replicas of ```a```.
-/
TheoremDoc Word.count_a_in_w as "count_a_in_w" in "Word"

/--
Subtracting any natural number from itself.

For any natural number ```n```, it means: ```n - n = 0```.
-/
TheoremDoc Nat.sub_self as "Nat.sub_self" in "Nat"

Statement count_a_in_w (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k) :
countCharInWord Character.a w = length w - n := by
  rewrite [w_eq_remaining_as_n_bs u v w z n k h_z z_eq h_k k_leq_n length_u_lt_k]
  rewrite [count_char_in_append]
  simp [count_char_in_replicateChar]
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  rewrite [Nat.add_sub_assoc]
  rewrite [Nat.sub_self]
  rewrite [Nat.add_zero]
  repeat rfl

Conclusion "Very good! Next, you will prove that ```w``` contains exactly ```n``` ```b```s."

NewTheorem Nat.sub_self
