import Game.Levels.AnBnNotRegular.L12_WEqRemainingAsNBs

namespace Word

World "AnBnNotRegular"
Level 13
Title ""

Introduction ""

TheoremDoc Word.count_a_in_w as "count_a_in_w" in "Word"

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

Conclusion ""
