import Game.Levels.AjBjNotRegular.L12_WEqRemainingAsNBs

namespace Word

World "AjBjNotRegular"
Level 13
Title "The Suffix w Contains (n - k) as"

Introduction "Using the theorem proved in the previous level, you will show that the suffix ```w```
of ```z = (u ++ v) ++ w``` contains ```n - k``` ```a```s."

/--
For a word $z = a^n b^n$, which is decomposed as ```z = (u ++ v) ++ w``` with
```k = length u + length v```, ```k ≤ n``` and ```length u < k```, the remaining
suffix ```w```contains exactly ```n - k``` replicas of ```a```.
-/
TheoremDoc Word.count_a_in_w as "count_a_in_w" in "AjBjNotRegular"

/--
Subtracting any natural number from itself.

For any natural number ```n```, it means: ```n - n = 0```.
-/
TheoremDoc Nat.sub_self as "Nat.sub_self" in "Nat"

Statement count_a_in_w (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length (u ++ v))
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.a w = length w - n := by
  Hint "In the previous level, you showed how many ```a```s and ```b```s occur in the word ```w```,
  you can use that theorem to simplify your current proof goal."
  Hint "In order to execute the tactic correctly, you have to pass the word ```w``` to that theorem
  as you did in one of the recent proofs and to avoid repetitive proofs for any other words, numbers
  or the hypotheses that theorem requires, you can pass those to the theorem as well. That makes
  your proof half as long."
  rewrite [w_eq_remaining_as_n_bs u v w z n k h_z z_eq h_k length_u_v_leq_n]
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
