import Game.Levels.AnBnNotRegular.L14_CountBInW

namespace Word

World "AnBnNotRegular"
Level 15
Title ""

Introduction ""

TheoremDoc Word.more_as_than_bs as "more_as_than_bs" in "Word"

Statement more_as_than_bs (u v w z z_pumped : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k)
(length_u_v_leq_n : length (u ++ v) ≤ n) (length_v_geq_1 : length v ≥ 1)
(h_z_pumped : z_pumped = (u ++ (replicateWord v 2)) ++ w) : (countCharInWord Character.b z_pumped) < countCharInWord Character.a z_pumped := by
  rewrite [h_z_pumped]
  repeat rewrite [replicateWord]
  repeat rewrite [append_nil]
  repeat rewrite [count_char_in_append]
  rewrite [count_a_in_u u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_b_in_u u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_a_in_v u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_b_in_v u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_a_in_w u v w z n k (z_eq := z_eq) (length_u_lt_k := length_u_lt_k) (k_leq_n :=
  k_leq_n)]
  rewrite [count_b_in_w u v w z n k (z_eq := z_eq) (length_u_lt_k := length_u_lt_k) (k_leq_n :=
  k_leq_n)]
  repeat rewrite [Nat.zero_add]
  rewrite [length_pumped_word u v w z n k (k_leq_n := k_leq_n)]
  apply Nat.lt_add_of_pos_right
  rewrite [<- Nat.add_zero 1] at length_v_geq_1
  rewrite [Nat.add_comm] at length_v_geq_1
  rewrite [<- Nat.succ_eq_add_one] at length_v_geq_1
  exact Nat.lt_of_succ_le length_v_geq_1
  exact z_eq
  repeat simp [h_z, h_k]

Conclusion ""
